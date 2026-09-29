module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.CoveringComponents
public import EremenkoLyubichConstant.CoveringSections

@[expose] public section

/-! # Regular neighborhoods on a full inverse component

Global inverse branches over a simply connected neighborhood stay in the full
inverse component where they start. A component whose image accumulates at a
regular target value therefore covers a neighborhood of that value.
-/

open Set Function Topology
open FunctionTheory

namespace SurfaceDynamics

theorem coveringOn_inverse_component_over_simplyConnected
    {E X : Type*} [TopologicalSpace E] [T2Space E] [LocallyConnectedSpace E]
    [TopologicalSpace X] {f : E → X} (hf : Continuous f)
    {D A : Set X} (hD : IsOpen D) (hA : IsOpen A) (hAD : A ⊆ D)
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    (hc : IsCoveringMapOn f A) (e₀ : E) :
    IsCoveringMapOn (fun z : connectedComponentIn (f ⁻¹' D) e₀ => f z) A := by
  let V := connectedComponentIn (f ⁻¹' D) e₀
  have hVo : IsOpen V := (hD.preimage hf).connectedComponentIn
  let p : V → X := fun z => f z
  have hpcont : Continuous p := hf.comp continuous_subtype_val
  have hplocal : IsLocalHomeomorphOn p (p ⁻¹' A) :=
    hc.isLocalHomeomorphOn.comp
      (hVo.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn.mono
        (subset_univ _)) (fun _ hx => hx)
  intro y hy
  apply isEvenlyCovered_of_sections hA hpcont hplocal _ hy
  intro e he
  let q : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨s, ⟨hs₀, hs⟩, _⟩ := hc.existsUnique_continuousMap_lifts q
    (a₀ := ⟨f e, he⟩) (e₀ := (e : E)) rfl (fun a => a.2)
  have hsrange : range s ⊆ f ⁻¹' D := by
    rintro _ ⟨a, rfl⟩
    change f (s a) ∈ D
    rw [show f (s a) = (a : X) from congrFun hs a]
    exact hAD a.2
  have hsmem (a : A) : s a ∈ V := by
    have hsub := (isPreconnected_range s.continuous).subset_connectedComponentIn
      (show (e : E) ∈ range s from ⟨⟨f e, he⟩, hs₀⟩) hsrange
    have ha := hsub (mem_range_self a)
    rwa [← connectedComponentIn_eq e.2] at ha
  refine ⟨⟨fun a => ⟨s a, hsmem a⟩, s.continuous.subtype_mk hsmem⟩, ?_, ?_⟩
  · intro a
    exact congrFun hs a
  · intro _
    exact Subtype.ext hs₀

theorem range_inverse_component_contains_regular_neighborhood
    {E X : Type*} [TopologicalSpace E] [T2Space E] [LocallyConnectedSpace E]
    [TopologicalSpace X] {f : E → X} (hf : Continuous f)
    {D A : Set X} (hD : IsOpen D) (hA : IsOpen A) (hAD : A ⊆ D)
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    (hc : IsCoveringMapOn f A) (e₀ : E) {y : X}
    (hyA : y ∈ A)
    (hy : y ∈ closure (range (fun z : connectedComponentIn (f ⁻¹' D) e₀ => f z))) :
    A ⊆ range (fun z : connectedComponentIn (f ⁻¹' D) e₀ => f z) := by
  let p : connectedComponentIn (f ⁻¹' D) e₀ → X := fun z => f z
  have hp := coveringOn_inverse_component_over_simplyConnected hf hD hA hAD hc e₀
  obtain ⟨b, hbA, e, heb⟩ := mem_closure_iff.mp hy A hA hyA
  have heA : p e ∈ A := by
    change f (e : E) = b at heb
    change f (e : E) ∈ A
    rw [heb]
    exact hbA
  intro a ha
  obtain ⟨w, hw⟩ := hp.isCoveringMap_restrictPreimage.surjective_connectedComponent
    (⟨e, heA⟩ : p ⁻¹' A) ⟨a, ha⟩
  exact ⟨((w : p ⁻¹' A) : connectedComponentIn (f ⁻¹' D) e₀), congrArg Subtype.val hw⟩

end SurfaceDynamics
