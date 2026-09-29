module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.FinitePunctureAreaBridge

@[expose] public section

/-! # Finite assembly of intrinsic chart estimates -/

open Set Function MeasureTheory
open scoped Manifold ENNReal
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]

theorem areaGain_finite_union_bound {U : TopologicalSpace.Opens M}
    (p : DiscCover M) (q : DiscCover U) {ι : Type*}
    (I : Finset ι) (E : Set U) (A : ι → Set U) (B : ι → ℝ≥0∞)
    (hcover : E ⊆ ⋃ i ∈ I, A i)
    (hbound : ∀ i ∈ I, p.areaGain q (A i) ≤ B i) :
    p.areaGain q E ≤ ∑ i ∈ I, B i := by
  calc
    p.areaGain q E ≤ p.areaGain q (⋃ i ∈ I, A i) := measure_mono hcover
    _ ≤ ∑ i ∈ I, p.areaGain q (A i) := measure_biUnion_finset_le I A
    _ ≤ ∑ i ∈ I, B i := by
      apply Finset.sum_le_sum
      intro i hi
      exact hbound i hi

end AreaDeficit.Surfaces.DiscCover

namespace AreaDeficit.Surfaces
variable {M : Type*} [TopologicalSpace M]

/-- A fixed ambient chart cover restricts to a cover of every punctured
remote domain, using only coordinates of actual chart punctures. -/
theorem finite_patch_cover_restrict {ι : Type*} (I : Finset ι)
    (c : ι → OpenPartialHomeomorph M ℂ) (A : ι → Set ℂ)
    (L : Set M) (hAt : ∀ i, A i ⊆ (c i).target)
    (hcover : L ⊆ ⋃ i ∈ I, (c i).symm '' A i)
    (P : Finset M) (U : TopologicalSpace.Opens M)
    (hU : ∀ x : M, x ∈ U ↔ x ∉ (↑P : Set M)) (hUN : Nonempty U)
    (W : TopologicalSpace.Opens U) (hWN : Nonempty W) :
    {w : W | ((w : U) : M) ∈ L} ⊆ ⋃ i ∈ I,
      (((c i).subtypeRestr hUN).subtypeRestr hWN).symm ''
        (A i \ (↑(chartPunctures (c i) P) : Set ℂ)) := by
  intro w hw
  obtain ⟨i,hi,z,hz,hzw⟩ := Set.mem_iUnion₂.mp (hcover hw)
  apply Set.mem_iUnion₂.mpr
  refine ⟨i,hi,?_⟩
  let d := (c i).subtypeRestr hUN
  let e := d.subtypeRestr hWN
  have hzt : z ∈ (c i).target := hAt i hz
  have hzP : z ∉ chartPunctures (c i) P := by
    intro hzP
    have hp : (c i).symm z ∈ P :=
      (mem_chartPunctures_iff (c i) P hzt).mp hzP
    have hwP : ((w : U) : M) ∈ P := hzw ▸ hp
    exact ((hU _).mp (w : U).property) hwP
  have hwsource : w ∈ e.source := by
    have hxsource : ((w : U) : M) ∈ (c i).source := by
      rw [← hzw]
      exact (c i).map_target hzt
    simpa only [e,d,OpenPartialHomeomorph.subtypeRestr_source,mem_preimage]
      using hxsource
  have heval : e w = z := by
    change (c i) ((w : U) : M) = z
    rw [← hzw]
    exact (c i).right_inv hzt
  have heq : e.symm z = w := by
    rw [← heval, e.left_inv hwsource]
  exact ⟨z,⟨hz,hzP⟩,heq⟩

end AreaDeficit.Surfaces



open Filter Metric Laplacian
open scoped Topology ContDiff
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]

/-- Assemble any fixed finite collection of ambient chart patches. The
covering hypothesis concerns only the set being measured and is uniform in
the finite puncture model. -/
theorem ambient_finite_patch_gain_bound (p : DiscCover M)
    {K C : Set M} (hK : IsClosed K) (hC : IsCompact C)
    (hCK : Disjoint C K) {ι : Type*} (I : Finset ι)
    (c : ι → OpenPartialHomeomorph M ℂ) (A D : ι → Set ℂ)
    (hc : ∀ i, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (c i) (c i).source)
    (hA : ∀ i, IsCompact (A i)) (hD : ∀ i, IsOpen (D i))
    (hAD : ∀ i, A i ⊆ D i) (hDc : ∀ i, D i ⊆ (c i).target)
    (hDC : ∀ i z, z ∈ D i → (c i).symm z ∈ C)
    (E : ∀ (_P : Finset M) (U : TopologicalSpace.Opens M)
      (W : TopologicalSpace.Opens U), Set W)
    (hcover : ∀ (P : Finset M) (U : TopologicalSpace.Opens M)
      (_hU : ∀ x : M, x ∈ U ↔ x ∉ (↑P : Set M)) (hUN : Nonempty U)
      (W : TopologicalSpace.Opens U)
      (_hW : ∀ x : U, x ∈ W ↔ (x : M) ∉ K) (hWN : Nonempty W),
      E P U W ⊆ ⋃ i ∈ I,
        (((c i).subtypeRestr hUN).subtypeRestr hWN).symm ''
          (A i \ (↑(AreaDeficit.Surfaces.chartPunctures (c i) P) : Set ℂ))) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (P : Finset M)
      (U : TopologicalSpace.Opens M)
      (_hU : ∀ x : M, x ∈ U ↔ x ∉ (↑P : Set M)) (_hUN : Nonempty U)
      (r : DiscCover U) (W : TopologicalSpace.Opens U)
      (_hW : ∀ x : U, x ∈ W ↔ (x : M) ∉ K) (_hWN : Nonempty W)
      (s : DiscCover W), r.areaGain s (E P U W) ≤ B := by
  have hlocal : ∀ i : ι, ∃ R : ℝ, ∀ (P : Finset M)
      (U : TopologicalSpace.Opens M)
      (hU : ∀ x : M, x ∈ U ↔ x ∉ (↑P : Set M)) (hUN : Nonempty U)
      (r : DiscCover U) (W : TopologicalSpace.Opens U)
      (hW : ∀ x : U, x ∈ W ↔ (x : M) ∉ K) (hWN : Nonempty W)
      (s : DiscCover W),
      r.areaGain s ((((c i).subtypeRestr hUN).subtypeRestr hWN).symm ''
        (A i \ (↑(AreaDeficit.Surfaces.chartPunctures (c i) P) : Set ℂ))) ≤
          ENNReal.ofReal R := by
    intro i
    exact p.ambient_intrinsic_chart_gain_finite_punctures
      hK hC hCK (c i) (hc i) (hA i) (hD i) (hAD i)
      (hDc i) (hDC i)
  choose R hR using hlocal
  refine ⟨∑ i ∈ I, ENNReal.ofReal (R i), ?_, ?_⟩
  · simp
  intro P U hU hUN r W hW hWN s
  exact areaGain_finite_union_bound r s I (E P U W)
    (fun i => (((c i).subtypeRestr hUN).subtypeRestr hWN).symm ''
      (A i \ (↑(AreaDeficit.Surfaces.chartPunctures (c i) P) : Set ℂ)))
    (fun i => ENNReal.ofReal (R i)) (hcover P U hU hUN W hW hWN)
    (fun i _ => hR i P U hU hUN r W hW hWN s)

end AreaDeficit.Surfaces.DiscCover

namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]

/-- The actual compact remote area estimate for finite puncture models,
provided by finitely many fixed compact ambient chart patches. -/
theorem remote_compact_gain_of_finite_patches (p : DiscCover M)
    {K C L : Set M} (hK : IsClosed K) (hC : IsCompact C)
    (hCK : Disjoint C K) {ι : Type*} (I : Finset ι)
    (c : ι → OpenPartialHomeomorph M ℂ) (A D : ι → Set ℂ)
    (hc : ∀ i, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (c i) (c i).source)
    (hA : ∀ i, IsCompact (A i)) (hD : ∀ i, IsOpen (D i))
    (hAD : ∀ i, A i ⊆ D i) (hDc : ∀ i, D i ⊆ (c i).target)
    (hDC : ∀ i z, z ∈ D i → (c i).symm z ∈ C)
    (hcover : L ⊆ ⋃ i ∈ I, (c i).symm '' A i) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (P : Finset M)
      (U : TopologicalSpace.Opens M)
      (_hU : ∀ x : M, x ∈ U ↔ x ∉ (↑P : Set M)) (_hUN : Nonempty U)
      (r : DiscCover U) (W : TopologicalSpace.Opens U)
      (_hW : ∀ x : U, x ∈ W ↔ (x : M) ∉ K) (_hWN : Nonempty W)
      (s : DiscCover W),
      r.areaGain s {w : W | ((w : U) : M) ∈ L} ≤ B := by
  exact p.ambient_finite_patch_gain_bound hK hC hCK I c A D hc hA hD
    hAD hDc hDC (fun _ _ W => {w : W | ((w : _) : M) ∈ L})
    (fun P U hU hUN W _ hWN =>
      AreaDeficit.Surfaces.finite_patch_cover_restrict I c A L
        (fun i => (hAD i).trans (hDc i)) hcover P U hU hUN W hWN)

end AreaDeficit.Surfaces.DiscCover
