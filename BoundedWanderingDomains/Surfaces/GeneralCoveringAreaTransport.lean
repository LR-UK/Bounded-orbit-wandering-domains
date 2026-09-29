module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.OpenDomainAreaTransport
public import BoundedWanderingDomains.Surfaces.CountableChartPartition
public import BoundedWanderingDomains.Surfaces.SurfacePolish
public import Mathlib.Data.Nat.Pairing

@[expose] public section

/-! # Intrinsic area transport between different ambient hyperbolic surfaces -/

open Set Function MeasureTheory
open scoped Manifold ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ) 1 N] [MeasurableSpace N] [BorelSpace N]
  [SecondCountableTopology N] [T2Space N]

theorem domainArea_eq_image_of_openDomain_covering_between_countable_patches
    (p : DiscCover M) (q : DiscCover N)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens N)
    (F : U → V) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hcov : IsCoveringMap F)
    {f : M → N} (hf : (fun x : U => f x) = (fun x => (F x : N)))
    (c : ℕ → OpenPartialHomeomorph M ℂ) (d : ℕ → OpenPartialHomeomorph N ℂ)
    (hc : ∀ i, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (c i) (c i).source)
    (hd : ∀ i, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (d i) (d i).source)
    (A : ℕ → Set M) {W : Set M}
    (hA : ∀ i, MeasurableSet (A i))
    (hfiA : ∀ i, MeasurableSet (f '' A i))
    (hAU : ∀ i, A i ⊆ U)
    (hAc : ∀ i, A i ⊆ (c i).source)
    (hfAd : ∀ i, f '' A i ⊆ (d i).source)
    (hsub : ∀ i, A i ⊆ W)
    (hdis : Pairwise (Disjoint on A))
    (hcover : (⋃ i, A i) = W) (hinj : InjOn f W) :
    p.domainArea U W = q.domainArea V (f '' W) := by
  have hlocal : ∀ i,
      p.domainArea U (A i) = q.domainArea V (f '' A i) := by
    intro i
    exact p.chart_domainArea_eq_image_of_openDomain_covering q U V F hF hcov hf
      (hc i) (hd i) (hA i) (hAU i) (hAc i) (hfAd i) (hfiA i)
      (hinj.mono (hsub i))
  have hdisImage : Pairwise (Disjoint on fun i => f '' A i) := by
    intro i j hij
    apply Set.disjoint_left.2
    rintro y ⟨x, hxi, rfl⟩ ⟨x', hxj, heq⟩
    have hxx : x = x' := hinj (hsub i hxi) (hsub j hxj) heq.symm
    subst x'
    exact Set.disjoint_left.mp (hdis hij) hxi hxj
  have hcoverImage : (⋃ i, f '' A i) = f '' W := by
    rw [← image_iUnion, hcover]
  calc
    p.domainArea U W = ∑' i, p.domainArea U (A i) := by
      rw [← hcover, measure_iUnion hdis hA]
    _ = ∑' i, q.domainArea V (f '' A i) := by
      congr 1
      funext i
      exact hlocal i
    _ = q.domainArea V (f '' W) := by
      rw [← measure_iUnion hdisImage hfiA, hcoverImage]


variable [LocallyCompactSpace M] [LocallyCompactSpace N]

theorem domainArea_eq_image_of_openDomain_covering_between
    (p : DiscCover M) (q : DiscCover N)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens N)
    (F : U → V) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hcov : IsCoveringMap F)
    {f : M → N} (hf : (fun x : U => f x) = (fun x => (F x : N)))
    (hfm : Measurable f) {W : Set M} (hW : MeasurableSet W)
    (hWU : W ⊆ U) (hinj : InjOn f W) :
    p.domainArea U W = q.domainArea V (f '' W) := by
  let : Nonempty M := ⟨p.projection discZero⟩
  let : Nonempty N := ⟨q.projection discZero⟩
  let : PolishSpace M := AreaDeficit.Surfaces.surfacePolishSpace
  let : PolishSpace N := AreaDeficit.Surfaces.surfacePolishSpace
  let P := Classical.choice (AreaDeficit.Surfaces.exists_chartPartition (M := M))
  let Q := Classical.choice (AreaDeficit.Surfaces.exists_chartPartition (M := N))
  let uv : ℕ → ℕ × ℕ := Nat.unpair
  let c : ℕ → OpenPartialHomeomorph M ℂ := fun k => P.chart (uv k).1
  let d : ℕ → OpenPartialHomeomorph N ℂ := fun k => Q.chart (uv k).2
  let A : ℕ → Set M := fun k =>
    W ∩ P.piece (uv k).1 ∩ f ⁻¹' Q.piece (uv k).2
  have hA : ∀ k, MeasurableSet (A k) := by
    intro k
    exact (hW.inter (P.measurable _)).inter ((Q.measurable _).preimage hfm)
  have hsub : ∀ k, A k ⊆ W := fun _ _ hx => hx.1.1
  have hdis : Pairwise (Disjoint on A) := by
    intro i j hij
    have huv : uv i ≠ uv j := by
      intro he
      apply hij
      calc
        i = Nat.pair (uv i).1 (uv i).2 := (Nat.pair_unpair i).symm
        _ = Nat.pair (uv j).1 (uv j).2 := congrArg (fun z => Nat.pair z.1 z.2) he
        _ = j := Nat.pair_unpair j
    have hcoord : (uv i).1 ≠ (uv j).1 ∨ (uv i).2 ≠ (uv j).2 := by
      by_cases hfst : (uv i).1 = (uv j).1
      · exact Or.inr (fun hsnd => huv (Prod.ext hfst hsnd))
      · exact Or.inl hfst
    rcases hcoord with hfst | hsnd
    · apply Set.disjoint_left.mpr
      intro x hxi hxj
      exact Set.disjoint_left.mp (P.disjoint hfst) hxi.1.2 hxj.1.2
    · apply Set.disjoint_left.mpr
      intro x hxi hxj
      exact Set.disjoint_left.mp (Q.disjoint hsnd) hxi.2 hxj.2
  have hcover : (⋃ k, A k) = W := by
    apply Subset.antisymm
    · exact iUnion_subset hsub
    · intro x hxW
      have hxP : x ∈ ⋃ n, P.piece n := by rw [P.covers]; trivial
      obtain ⟨n, hxn⟩ := mem_iUnion.mp hxP
      have hxQ : f x ∈ ⋃ m, Q.piece m := by rw [Q.covers]; trivial
      obtain ⟨m, hxm⟩ := mem_iUnion.mp hxQ
      apply mem_iUnion.mpr
      refine ⟨Nat.pair n m, ?_⟩
      simpa only [A, uv, Nat.unpair_pair] using ⟨⟨hxW, hxn⟩, hxm⟩
  have hfA : ∀ k, MeasurableSet (f '' A k) := by
    have hfcont : ContinuousOn f U := by
      rw [continuousOn_iff_continuous_domRestrict]
      change Continuous (fun x : U => f x)
      rw [hf]
      exact continuous_subtype_val.comp hF.continuous
    intro k
    exact (hA k).image_of_continuousOn_injOn
      (hfcont.mono (fun _ hx => hWU (hsub k hx)))
      (hinj.mono (hsub k))
  apply p.domainArea_eq_image_of_openDomain_covering_between_countable_patches q
    U V F hF hcov hf c d (fun k => P.holomorphic _) (fun k => Q.holomorphic _)
    A hA hfA
  · exact fun _ _ hx => hWU hx.1.1
  · exact fun k _ hx => P.subordinate _ hx.1.2
  · intro k
    rintro _ ⟨x, hx, rfl⟩
    exact Q.subordinate _ hx.2
  · exact hsub
  · exact hdis
  · exact hcover
  · exact hinj


end AreaDeficit.Surfaces.DiscCover
