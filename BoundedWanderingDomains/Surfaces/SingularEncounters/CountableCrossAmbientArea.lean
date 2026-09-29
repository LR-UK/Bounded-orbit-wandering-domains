module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.CrossAmbientAreaAdvance
public import BoundedWanderingDomains.Surfaces.SingularEncounters.CrossAmbientGainBudget
public import BoundedWanderingDomains.Surfaces.SingularEncounters.CountableAreaBudget
public import BoundedWanderingDomains.Surfaces.SingularEncounters.MeasurableCoverPartition

@[expose] public section

/-! # Summing area budgets computed in different ambient target surfaces -/

open Set Function MeasureTheory Topology
open AreaDeficit.Surfaces
open scoped Manifold ENNReal

namespace SurfaceDynamics.LocalMap

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [T2Space M] [LocallyCompactSpace M] [DecidableEq M]
  {ι : Type*} [Fintype ι] {N : ι → Type*}
  [∀ i, TopologicalSpace (N i)] [∀ i, ChartedSpace ℂ (N i)]
  [∀ i, IsManifold 𝓘(ℂ) 1 (N i)] [∀ i, MeasurableSpace (N i)] [∀ i, BorelSpace (N i)]
  [∀ i, SecondCountableTopology (N i)] [∀ i, T2Space (N i)] [∀ i, LocallyCompactSpace (N i)]

theorem exists_uniform_countable_cross_ambient_area_advance
    (f : LocalMap M) (hf : IsOpenHolomorphic f) (p : DiscCover M)
    (q : ∀ i, DiscCover (N i)) (j : ∀ i, M → N i)
    (hj : ∀ i, IsOpenEmbedding (j i))
    (hjh : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (j i))
    (D : ∀ i, TopologicalSpace.Opens (N i)) (E : Finset M)
    (L : ∀ i, Set (N i)) (hL : ∀ i, IsCompact (L i)) (hLD : ∀ i, L i ⊆ D i) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (V : ℕ → TopologicalSpace.Opens M) (hV : ∀ n, (V n : Set M) ⊆ f.source)
        (label : ℕ → ι),
      (∀ n, ((j (label n)) ⁻¹' (D (label n) : Set (N (label n)))) \ (E : Set M) ⊆
        (f.restrictSource (V n) (hV n)).regularValues) →
      ∀ P : Finset M,
      (∀ x : f.source, (x : M) ∈ P → f.map x ∈ (P ∪ E : Finset M)) →
      ∀ A : ℕ → Set M, (∀ n, MeasurableSet (A n)) → Pairwise (Disjoint on A) →
      (∀ n, A n ⊆ V n) → InjOn f.totalize (⋃ n, A n) →
      (∀ n, j (label n) '' (f.totalize '' A n) ⊆ L (label n)) →
      (∀ n x, x ∈ A n → f.totalize x ∉ P ∧ f.totalize x ∉ E) →
      p.domainArea (finitePunctureDomain P) (⋃ n, A n) ≤
        p.domainArea (finitePunctureDomain P) (f.totalize '' (⋃ n, A n)) + C := by
  classical
  choose B hB hb using fun i => exists_uniform_cross_ambient_gain_budget
    (q i) (j i) (hj i) (D i) E (hL i) (hLD i)
  refine ⟨∑ i, B i, ENNReal.sum_ne_top.mpr (fun i _ => hB i), ?_⟩
  intro V hV label hreg P hforward A hA hdis hAV hinj himage havoid
  let U := finitePunctureDomain P
  let Y : ι → TopologicalSpace.Opens M := fun i => finiteRemovalDomain U E ⊓
    ⟨j i ⁻¹' (D i : Set (N i)), (D i).isOpen.preimage (hj i).continuous⟩
  let gain : ι → Measure M := fun i => ((q i).domainAreaGain
    ⟨j i '' (U : Set M), (hj i).isOpenMap _ U.isOpen⟩
    ⟨j i '' (Y i : Set M), (hj i).isOpenMap _ (Y i).isOpen⟩).comap (j i)
  let inner : ι → Set M := fun i => j i ⁻¹' L i
  have hinner : ∀ i, MeasurableSet (inner i) := fun i =>
    (hL i).measurableSet.preimage (hj i).continuous.measurable
  have hsub : ∀ n, A n ⊆ ⋃ k, A k := fun n => subset_iUnion A n
  have him : ∀ n, MeasurableSet (f.totalize '' A n) := by
    let : PolishSpace M := surfacePolishSpace
    intro n
    exact (hA n).image_of_continuousOn_injOn
      ((f.continuousOn_totalize hf.2.continuous).mono ((hAV n).trans (hV n)))
      (hinj.mono (hsub n))
  have hdisim : Pairwise (Disjoint on fun n => f.totalize '' A n) := by
    intro n m hnm
    apply disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, he⟩
    have hxz := hinj (hsub n hx) (hsub m hz) he.symm
    subst z
    exact disjoint_left.mp (hdis hnm) hx hz
  have himinner : ∀ n, f.totalize '' A n ⊆ inner (label n) := by
    intro n y hy
    exact himage n ⟨y, hy, rfl⟩
  have hstep : ∀ n, p.domainArea U (A n) ≤
      p.domainArea U (f.totalize '' A n) + gain (label n) (f.totalize '' A n) := by
    intro n
    exact f.restricted_area_le_add_cross_ambient_gain hf p (q (label n))
      (j (label n)) (hj (label n)) (hjh (label n)) (D (label n)) E (V n) (hV n)
      (hreg n) P hforward (hA n) (hAV n) (hinj.mono (hsub n))
      ((himage n).trans (hLD (label n))) (havoid n)
  have hsum := AreaDeficit.area_advance_of_countable_local_budgets
    (p.domainArea U) (p.domainArea U) gain A (fun n => f.totalize '' A n) label inner
    hA him hinner hdis hdisim himinner hstep
  rw [← image_iUnion] at hsum
  exact hsum.trans (add_le_add le_rfl (Finset.sum_le_sum fun i _ => hb i U))

theorem exists_uniform_cross_ambient_area_advance_on_cover
    (f : LocalMap M) (hf : IsOpenHolomorphic f) (p : DiscCover M)
    (q : ∀ i, DiscCover (N i)) (j : ∀ i, M → N i)
    (hj : ∀ i, IsOpenEmbedding (j i))
    (hjh : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (j i))
    (D : ∀ i, TopologicalSpace.Opens (N i)) (E : Finset M)
    (L : ∀ i, Set (N i)) (hL : ∀ i, IsCompact (L i)) (hLD : ∀ i, L i ⊆ D i) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (V : ℕ → TopologicalSpace.Opens M) (hV : ∀ n, (V n : Set M) ⊆ f.source)
        (label : ℕ → ι),
      (∀ n, ((j (label n)) ⁻¹' (D (label n) : Set (N (label n)))) \ (E : Set M) ⊆
        (f.restrictSource (V n) (hV n)).regularValues) →
      ∀ P : Finset M,
      (∀ x : f.source, (x : M) ∈ P → f.map x ∈ (P ∪ E : Finset M)) →
      ∀ W : Set M, MeasurableSet W → InjOn f.totalize W →
      W ⊆ ⋃ n, (V n : Set M) ∩ (j (label n) ∘ f.totalize) ⁻¹' L (label n) →
      (∀ x ∈ W, f.totalize x ∉ P ∧ f.totalize x ∉ E) →
      p.domainArea (finitePunctureDomain P) W ≤
        p.domainArea (finitePunctureDomain P) (f.totalize '' W) + C := by
  obtain ⟨C, hC, hstep⟩ := f.exists_uniform_countable_cross_ambient_area_advance
    hf p q j hj hjh D E L hL hLD
  refine ⟨C, hC, ?_⟩
  intro V hV label hreg P hforward W hW hinj hcover havoid
  let B : ℕ → Set M := fun n => (V n : Set M) ∩ (j (label n) ∘ f.totalize) ⁻¹' L (label n)
  have hB : ∀ n, MeasurableSet (B n) := fun n =>
    (V n).isOpen.measurableSet.inter ((hL (label n)).measurableSet.preimage
      ((hj (label n)).continuous.measurable.comp (f.measurable_totalize hf.2.continuous)))
  obtain ⟨A, hA, hdis, hAB, hunion⟩ := measurable_partition_of_countable_cover hW B hB hcover
  have hAW : ∀ n, A n ⊆ W := fun n => hunion ▸ subset_iUnion A n
  have him : ∀ n, j (label n) '' (f.totalize '' A n) ⊆ L (label n) := by
    rintro n y ⟨v, ⟨x, hx, rfl⟩, rfl⟩
    exact (hAB n hx).2
  have hh := hstep V hV label hreg P hforward A hA hdis
    (fun n => (hAB n).trans inter_subset_left) (hunion.symm ▸ hinj) him
    (fun n x hx => havoid x (hAW n hx))
  simpa only [hunion] using hh

end SurfaceDynamics.LocalMap
