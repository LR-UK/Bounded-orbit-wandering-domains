module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.ComponentRestriction
public import BoundedWanderingDomains.Surfaces.LocalCompactCovering

@[expose] public section

/-! # Finite singular obstructions in compact source models -/

open Set Function Topology
open AreaDeficit.Surfaces
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [LocallyCompactSpace X] [T2Space X] [DecidableEq X]

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [LocallyCompactSpace X]
  [T2Space X] [DecidableEq X] in
theorem interiorRestriction_coveringOn
    (f : LocalMap X) (hf : Continuous f.map) {K : Set X}
    (hK : IsCompact K) (hKs : K ⊆ f.source)
    (A : TopologicalSpace.Opens X)
    (hint : ∀ z ∈ f.sourceCompact K, f.map z ∈ A → z ∈ interior (f.sourceCompact K))
    (hcov : IsCoveringMapOn (fun z : f.sourceCompact K => f.map z) A) :
    IsCoveringMapOn (f.restrictSource ⟨interior K, isOpen_interior⟩
      (fun _ hx => hKs (interior_subset hx))).map A := by
  let V : TopologicalSpace.Opens X := ⟨interior K, isOpen_interior⟩
  let r := f.restrictSource V (fun _ hx => hKs (interior_subset hx))
  let W := compactCoverDomain (f.sourceCompact K) A f.map hf
  let P : Set r.source := r.map ⁻¹' (A : Set X)
  have hInt : (Subtype.val : f.source → X) ⁻¹' interior K =
      interior (f.sourceCompact K) :=
    f.source.isOpen.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
      continuous_subtype_val K
  let e : P ≃ₜ W :=
    { toFun := fun z => ⟨⟨z.1, hKs (interior_subset z.1.2)⟩,
        hInt ▸ z.1.2, z.2⟩
      invFun := fun z => ⟨⟨z.1, by
        change (z.1 : X) ∈ interior K
        exact show z.1 ∈ (Subtype.val : f.source → X) ⁻¹' interior K from
          hInt.symm ▸ z.2.1⟩, z.2.2⟩
      left_inv := fun z => Subtype.ext (Subtype.ext rfl)
      right_inv := fun z => Subtype.ext (Subtype.ext rfl)
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hc := (compact_interior_isCoveringMap A
    (f.sourceCompact_isCompact hK hKs) hf hint hcov).comp_homeomorph e
  apply IsCoveringMapOn.of_isCoveringMap_restrictPreimage (A : Set X) A.isOpen
    (A.isOpen.preimage (hf.comp (continuous_subtype_val.subtype_mk _)))
  exact hc

/-- Once a full inverse component is confined to the interior of a compact
source model, its singular obstructions lie in the model's finite branch set,
provided its target disc avoids the image of the model boundary. -/
theorem exists_finite_component_obstructions_in_compact
    (f : LocalMap X) (hf : IsOpenHolomorphic f) {K : Set X}
    (hK : IsCompact K) (hKs : K ⊆ f.source) :
    ∃ E : Finset X, ∀ (D : TopologicalSpace.Opens X) (a : f.source),
      f.map a ∈ D →
      (D : Set X) ⊆ (f.map '' frontier (f.sourceCompact K))ᶜ →
      (f.inverseComponentSource hf.2.continuous D a : Set X) ⊆ interior K →
      f.componentSingularValues hf.2.continuous D a ⊆ E := by
  let sourceLocallyCompact : LocallyCompactSpace f.source :=
    f.source.isOpen.locallyCompactSpace
  obtain ⟨E, hE⟩ := exists_finite_branch_values_compact_covering hf.2 hf.1
    (f.sourceCompact_isCompact hK hKs)
  refine ⟨E, ?_⟩
  intro D a ha hD hC y hy
  by_contra hyE
  let V : TopologicalSpace.Opens X := ⟨interior K, isOpen_interior⟩
  have hVs : (V : Set X) ⊆ f.source := fun _ hx => hKs (interior_subset hx)
  let r := f.restrictSource V hVs
  let hc := hf.2.continuous.comp (continuous_subtype_val.subtype_mk (fun x : V => hVs x.2))
  have haV : (a : X) ∈ V := hC ⟨a, mem_connectedComponentIn ha, rfl⟩
  let b : r.source := ⟨a, haV⟩
  have heq := f.componentSingularValues_restrictSource_eq_of_component_subset
    hf.2.continuous V hVs D b ha hC
  have hyr : y ∈ r.componentSingularValues hc D b := heq.symm ▸ hy
  obtain ⟨Q, hQ, hQsub⟩ := exists_coordDisk_center_closedCarrier_subset
    (D.isOpen.inter E.finite_toSet.isClosed.isOpen_compl) ⟨hy.2, hyE⟩
  let A : TopologicalSpace.Opens X := ⟨range Q.param, Q.isOpenEmbedding_param.isOpen_range⟩
  have hAsub : (A : Set X) ⊆ (D : Set X) ∩ (E : Set X)ᶜ := by
    rintro v ⟨w, rfl⟩
    exact hQsub (Q.param_mem_closedCarrier w)
  have hint : ∀ z ∈ f.sourceCompact K, f.map z ∈ A →
      z ∈ interior (f.sourceCompact K) := by
    intro z hz hza
    by_contra hzi
    have hzfront : z ∈ frontier (f.sourceCompact K) := by
      rw [frontier, (f.sourceCompact_isCompact hK hKs).isClosed.closure_eq]
      exact ⟨hz, hzi⟩
    exact hD (hAsub hza).1 ⟨z, hzfront, rfl⟩
  have hcov := f.interiorRestriction_coveringOn hf.2.continuous hK hKs A hint
    (hE A (fun _ hx => (hAsub hx).2) hint)
  let e : unitDisc ≃ₜ A := Q.isOpenEmbedding_param.isEmbedding.toHomeomorph
  let discSimplyConnected : SimplyConnectedSpace unitDisc := unitDisc_simplyConnected
  let targetSimplyConnected : SimplyConnectedSpace A :=
    e.symm.toHomotopyEquiv.simplyConnectedSpace
  let targetLocallyPathConnected : LocallyPathConnectedSpace A :=
    ChartedSpace.locallyPathConnectedSpace ℂ A
  have hyA : y ∈ A := ⟨discZero, Q.param_zero.trans hQ⟩
  exact hyr.1.1 (r.inverseComponent_regularValues_of_regular_neighborhood hc D A
    (fun _ hx => (hAsub hx).1) hcov b hyA hyr.1.2 hyA)

end SurfaceDynamics.LocalMap
