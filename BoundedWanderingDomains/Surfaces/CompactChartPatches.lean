module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.FinitePatchAssembly

@[expose] public section

/-! # Finite compact chart patches around a compact surface set -/

open Set Function Filter MeasureTheory
open scoped Manifold Topology ENNReal
namespace AreaDeficit.Surfaces
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

omit [IsManifold 𝓘(ℂ) 1 M] in
/-- Inside a compact neighbourhood, any compact set is covered by finitely
many compact coordinate patches with slightly larger open chart supports. -/
theorem compact_finite_chart_patches [LocallyCompactSpace M]
    {L C : Set M} (hL : IsCompact L) (hLC : L ⊆ interior C) :
    ∃ (I : Finset L) (A D : L → Set ℂ),
      (∀ x, IsCompact (A x)) ∧ (∀ x, IsOpen (D x)) ∧
      (∀ x, A x ⊆ D x) ∧
      (∀ x, D x ⊆ (chartAt ℂ (x : M)).target) ∧
      (∀ x z, z ∈ D x → (chartAt ℂ (x : M)).symm z ∈ C) ∧
      L ⊆ ⋃ x ∈ I, (chartAt ℂ (x : M)).symm '' A x := by
  let c : L → OpenPartialHomeomorph M ℂ := fun x => chartAt ℂ (x : M)
  let D : L → Set ℂ := fun x => (c x).target ∩ (c x).symm ⁻¹' interior C
  have hD : ∀ x : L, IsOpen (D x) := by
    intro x
    exact (c x).isOpen_inter_preimage_symm isOpen_interior
  have hxD : ∀ x : L, (c x) x ∈ D x := by
    intro x
    have hxsource : (x : M) ∈ (c x).source := ChartedSpace.mem_chart_source _
    exact ⟨(c x).map_source hxsource, by
      change (c x).symm ((c x) (x : M)) ∈ interior C
      rw [(c x).left_inv hxsource]
      exact hLC x.property⟩
  have hpatch : ∀ x : L, ∃ A : Set ℂ,
      IsCompact A ∧ (c x) x ∈ interior A ∧ A ⊆ D x := by
    intro x
    exact exists_compact_subset (hD x) (hxD x)
  choose A hA hxA hAD using hpatch
  let O : L → Set M := fun x => (c x).source ∩ (c x) ⁻¹' interior (A x)
  have hO : ∀ x : L, IsOpen (O x) :=
    fun x => (c x).isOpen_inter_preimage isOpen_interior
  have hLO : L ⊆ ⋃ x : L, O x := by
    intro y hy
    apply Set.mem_iUnion.mpr
    refine ⟨⟨y,hy⟩, ?_⟩
    exact ⟨ChartedSpace.mem_chart_source _, hxA ⟨y,hy⟩⟩
  obtain ⟨I,hLI⟩ := hL.elim_finite_subcover O hO hLO
  refine ⟨I,A,D,hA,hD,hAD,?_,?_,?_⟩
  · intro x z hz
    exact hz.1
  · intro x z hz
    exact interior_subset hz.2
  · intro y hy
    obtain ⟨x,hx,hyo⟩ := Set.mem_iUnion₂.mp (hLI hy)
    apply Set.mem_iUnion₂.mpr
    refine ⟨x,hx,?_⟩
    refine ⟨(c x) y, interior_subset hyo.2, ?_⟩
    exact (c x).left_inv hyo.1

end AreaDeficit.Surfaces

namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [LocallyCompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- Compact remote removal has a uniform finite intrinsic area-gain bound
through all finite puncture models of a hyperbolic ambient surface. -/
theorem remote_compact_gain_finite_puncture_models (p : DiscCover M)
    {K L : Set M} (hK : IsClosed K) (hL : IsCompact L)
    (hLK : Disjoint L K) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (P : Finset M)
      (U : TopologicalSpace.Opens M)
      (_hU : ∀ x : M, x ∈ U ↔ x ∉ (↑P : Set M)) (_hUN : Nonempty U)
      (r : DiscCover U) (W : TopologicalSpace.Opens U)
      (_hW : ∀ x : U, x ∈ W ↔ (x : M) ∉ K) (_hWN : Nonempty W)
      (s : DiscCover W),
      r.areaGain s {w : W | ((w : U) : M) ∈ L} ≤ B := by
  have hLK' : L ⊆ Kᶜ := by
    intro x hx hxK
    exact disjoint_left.mp hLK hx hxK
  obtain ⟨C,hC,hLC,hCKsub⟩ :=
    exists_compact_between hL hK.isOpen_compl hLK'
  have hCK : Disjoint C K := disjoint_left.mpr (by
    intro x hx hxK
    exact hCKsub hx hxK)
  obtain ⟨I,A,D,hA,hD,hAD,hDc,hDC,hcover⟩ :=
    AreaDeficit.Surfaces.compact_finite_chart_patches hL hLC
  exact p.remote_compact_gain_of_finite_patches hK hC hCK I
    (fun x => chartAt ℂ (x : M)) A D
    (fun x => (mdifferentiable_chart (I := 𝓘(ℂ)) (x : M)).1)
    hA hD hAD hDc hDC hcover

end AreaDeficit.Surfaces.DiscCover
