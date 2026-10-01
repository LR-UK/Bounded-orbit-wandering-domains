module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.InverseComponentCovering
public import BoundedWanderingDomains.Surfaces.CoordinateDiscParam
public import BoundedWanderingDomains.Surfaces.CoordinateDiskSelection

@[expose] public section

/-! # Restricting coverings to unions of ambient components

A clopen restriction of the source retains complete inverse sheets. Empty
sheets are allowed throughout, as required by the public regular-value definition.
-/

open Set Function Topology
open FunctionTheory AreaDeficit.Surfaces
open scoped Manifold

namespace SurfaceDynamics

theorem coveringOn_clopen_source_over_simplyConnected
    {E X : Type*} [TopologicalSpace E] [T2Space E] [TopologicalSpace X]
    {f : E → X} (hf : Continuous f) {S : Set E} (hS : IsClopen S)
    {A : Set X} (hA : IsOpen A)
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    (hc : IsCoveringMapOn f A) : IsCoveringMapOn (fun x : S => f x) A := by
  let p : S → X := fun x => f x
  have hpcont : Continuous p := hf.comp continuous_subtype_val
  have hplocal : IsLocalHomeomorphOn p (p ⁻¹' A) :=
    hc.isLocalHomeomorphOn.comp
      (hS.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn.mono
        (subset_univ _)) (fun _ hx => hx)
  intro y hy
  apply isEvenlyCovered_of_sections hA hpcont hplocal _ hy
  intro e he
  let q : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨s, ⟨hs₀, hs⟩, _⟩ := hc.existsUnique_continuousMap_lifts q
    (a₀ := ⟨f e, he⟩) (e₀ := (e : E)) rfl (fun a => a.2)
  have hsmem (a : A) : s a ∈ S := by
    have hsub := (isPreconnected_range s.continuous).subset_connectedComponent
      (show (e : E) ∈ range s from ⟨⟨f e, he⟩, hs₀⟩)
    exact hS.connectedComponent_subset e.property (hsub (mem_range_self a))
  refine ⟨⟨fun a => ⟨s a, hsmem a⟩, s.continuous.subtype_mk hsmem⟩, ?_, ?_⟩
  · intro a
    exact congrFun hs a
  · intro _
    exact Subtype.ext hs₀

theorem coveringOn_clopen_source
    {E X : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {f : E → X} (hf : Continuous f) {S : Set E} (hS : IsClopen S)
    {U : Set X} (hU : IsOpen U) (hc : IsCoveringMapOn f U) :
    IsCoveringMapOn (fun x : S => f x) U := by
  intro y hy
  obtain ⟨D, hDy, hDU⟩ := exists_coordDisk_center_closedCarrier_subset hU hy
  let A : TopologicalSpace.Opens X := ⟨range D.param, D.isOpenEmbedding_param.isOpen_range⟩
  let e : unitDisc ≃ₜ A := D.isOpenEmbedding_param.toIsEmbedding.toHomeomorph
  let : SimplyConnectedSpace unitDisc := unitDisc_simplyConnected
  let : SimplyConnectedSpace A := e.symm.toHomotopyEquiv.simplyConnectedSpace
  let : LocallyPathConnectedSpace A := ChartedSpace.locallyPathConnectedSpace ℂ A
  have hAU : (A : Set X) ⊆ U := by
    rintro _ ⟨z, rfl⟩
    exact hDU (D.param_mem_closedCarrier z)
  have hyA : y ∈ A := ⟨discZero, D.param_zero.trans hDy⟩
  exact coveringOn_clopen_source_over_simplyConnected hf hS A.isOpen (hc.mono hAU) y hyA

theorem covering_clopen_source
    {E X : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {f : E → X} (hc : IsCoveringMap f) {S : Set E} (hS : IsClopen S) :
    IsCoveringMap (fun x : S => f x) := by
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  exact coveringOn_clopen_source hc.continuous hS isOpen_univ
    (isCoveringMap_iff_isCoveringMapOn_univ.mp hc)

end SurfaceDynamics
