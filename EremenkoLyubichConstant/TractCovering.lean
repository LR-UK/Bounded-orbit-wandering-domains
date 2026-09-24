/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

import EremenkoLyubichConstant.CoveringSections
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.LocallyConvex.WithSeminorms

open Set Function Metric
open scoped Topology

namespace FunctionTheory

/-- Taking a component after pulling back a component gives the component of the full preimage. -/
theorem connectedComponentIn_preimage_connectedComponentIn
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {g : X → Y} (hg : Continuous g) {U : Set Y} {x : X} (hx : g x ∈ U) :
    connectedComponentIn (g ⁻¹' connectedComponentIn U (g x)) x =
      connectedComponentIn (g ⁻¹' U) x := by
  apply Subset.antisymm
  · exact connectedComponentIn_mono x (preimage_mono (connectedComponentIn_subset U (g x)))
  · apply isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn (show x ∈ g ⁻¹' U from hx))
    intro z hz
    exact connectedComponentIn_mono (g x) (image_preimage_subset g U)
      (hg.continuousOn.mapsTo_connectedComponentIn (show x ∈ g ⁻¹' U from hx) hz)

/-- A connected covering of a simply connected, locally path-connected space is a homeomorphism. -/
theorem exists_homeomorph_of_simplyConnected_base
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [PreconnectedSpace E] [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {p : E → X} (hp : IsCoveringMap p) (e₀ : E) :
    ∃ h : E ≃ₜ X, (h : E → X) = p := by
  obtain ⟨G, ⟨hG₀, hG⟩, _⟩ := hp.existsUnique_continuousMap_lifts
    (⟨id, continuous_id⟩ : C(X, X)) (p e₀) e₀ rfl
  have hGp : G ∘ p = id := by
    apply hp.eq_of_comp_eq (G.continuous.comp hp.continuous) continuous_id _ e₀ hG₀
    funext e
    exact congrFun hG (p e)
  exact ⟨{ toFun := p, invFun := G
           left_inv := fun e ↦ congrFun hGp e
           right_inv := fun x ↦ congrFun hG x
           continuous_toFun := hp.continuous
           continuous_invFun := G.continuous }, rfl⟩

/-- Restricting a plane covering over an open set to a preimage component is still a covering.
No holomorphicity, simple connectivity, or finiteness assumption is used. -/
theorem isCoveringMapOn_connectedComponentIn
    {f : ℂ → ℂ} {U : Set ℂ} (hf : Continuous f) (hU : IsOpen U)
    (hc : IsCoveringMapOn f U) (z₀ : ℂ) :
    IsCoveringMapOn (fun z : connectedComponentIn (f ⁻¹' U) z₀ ↦ f z) U := by
  let T := connectedComponentIn (f ⁻¹' U) z₀
  have hT : IsOpen T := (hU.preimage hf).connectedComponentIn
  let p : T → ℂ := fun z ↦ f z
  have hpcont : Continuous p := hf.comp continuous_subtype_val
  have hplocal : IsLocalHomeomorph p :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr <|
      hc.isLocalHomeomorphOn.comp hT.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
        (fun z _ ↦ connectedComponentIn_subset (f ⁻¹' U) z₀ z.2)
  intro y hy
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU y hy
  let V := ball y r
  let : ContractibleSpace V := (convex_ball y r).contractibleSpace ⟨y, mem_ball_self hr⟩
  let : LocallyPathConnectedSpace V := isOpen_ball.locallyPathConnectedSpace
  apply isEvenlyCovered_of_sections (U := V) isOpen_ball hpcont
    (hplocal.isLocalHomeomorphOn.mono (subset_univ _)) _ (mem_ball_self hr)
  intro e he
  let q : C(V, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨s, ⟨hs₀, hs⟩, _⟩ := hc.existsUnique_continuousMap_lifts q
    (a₀ := ⟨f e, he⟩) (e₀ := (e : ℂ)) rfl (fun v ↦ hball v.2)
  have hsrange : range s ⊆ f ⁻¹' U := by
    rintro _ ⟨v, rfl⟩
    change f (s v) ∈ U
    rw [show f (s v) = (v : ℂ) from congrFun hs v]
    exact hball v.2
  have hsmem (v : V) : s v ∈ T := by
    have hsub := (isPreconnected_range s.continuous).subset_connectedComponentIn
      (show (e : ℂ) ∈ range s from ⟨⟨f e, he⟩, hs₀⟩) hsrange
    have hv := hsub (mem_range_self v)
    rwa [← connectedComponentIn_eq e.2] at hv
  refine ⟨⟨fun v ↦ ⟨s v, hsmem v⟩, s.continuous.subtype_mk hsmem⟩, ?_, ?_⟩
  · intro v
    exact congrFun hs v
  · intro h
    exact Subtype.ext hs₀

/-- The covering projection on a preimage component, with its natural codomain. -/
theorem isCoveringMap_connectedComponentIn
    {f : ℂ → ℂ} {U : Set ℂ} (hf : Continuous f) (hU : IsOpen U)
    (hc : IsCoveringMapOn f U) (z₀ : ℂ) :
    IsCoveringMap (fun z : connectedComponentIn (f ⁻¹' U) z₀ ↦
      (⟨f z, connectedComponentIn_subset (f ⁻¹' U) z₀ z.2⟩ : U)) := by
  let T := connectedComponentIn (f ⁻¹' U) z₀
  let p : T → ℂ := fun z ↦ f z
  let e : T ≃ₜ (p ⁻¹' U) :=
    { toFun := fun z ↦ ⟨z, connectedComponentIn_subset (f ⁻¹' U) z₀ z.2⟩
      invFun := Subtype.val
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := continuous_id.subtype_mk _
      continuous_invFun := continuous_subtype_val }
  exact (isCoveringMapOn_connectedComponentIn hf hU hc z₀).isCoveringMap_restrictPreimage.comp_homeomorph e

end FunctionTheory
