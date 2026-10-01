module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ClopenNormality
public import BoundedWanderingDomains.Surfaces.Disconnected.ClopenSourceRestriction
public import BoundedWanderingDomains.Surfaces.BKL.ComponentRecovery

@[expose] public section

/-! # Normality components retained by source and clopen ambient restrictions -/

open Set Function Topology TopologicalSpace

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [T2Space X] [LocallyCompactSpace X]

theorem isComponent_restrictSource_of_trapped
    (f : LocalMap X) (V : Opens X) (hV : (V : Set X) ⊆ f.source)
    {U : Set X} (hU : f.IsComponent U) (hUt : U ⊆ (f.restrictSource V hV).trapped) :
    (f.restrictSource V hV).IsComponent U := by
  let r := f.restrictSource V hV
  let : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  obtain ⟨a, ha, hUa⟩ := hU
  have haU : a ∈ U := hUa.symm ▸ mem_connectedComponentIn ha
  have hUo : IsOpen U := hUa.symm ▸ f.isOpen_omega.connectedComponentIn
  have hUω : U ⊆ f.omega := hUa.symm ▸ connectedComponentIn_subset _ _
  have hUr : U ⊆ r.omega := by
    intro x hx
    obtain ⟨W, hWo, hxW, _, hn⟩ := hUω hx
    refine ⟨W ∩ U, hWo.inter hUo, ⟨hxW, hx⟩, inter_subset_right.trans hUt, ?_⟩
    exact f.isNormalOn_restrictSource_of_trapped V hV (inter_subset_right.trans hUt)
      (f.isNormalOn_mono inter_subset_left hn)
  refine ⟨a, hUr haU, ?_⟩
  apply Subset.antisymm
  · apply (hUa.symm ▸ isPreconnected_connectedComponentIn).subset_connectedComponentIn haU hUr
  · rw [hUa]
    exact connectedComponentIn_mono a (f.restrictSource_omega_subset V hV)

omit [ChartedSpace ℂ X] in
theorem isComponent_restrictAmbient_of_isClosed
    (f : LocalMap X) (O : Opens X) [LocallyCompactSpace O]
    (hO : IsClosed (O : Set X)) (hsource : (f.source : Set X) ⊆ O)
    (hmap : ∀ x : f.source, f.map x ∈ O)
    {U : Set X} (hU : f.IsComponent U) :
    (f.restrictAmbient O hsource hmap).IsComponent ((Subtype.val : O → X) ⁻¹' U) := by
  let g := f.restrictAmbient O hsource hmap
  have hω := f.omega_restrictAmbient_eq_preimage_of_isClosed O hO hsource hmap
  have him : (Subtype.val : O → X) '' g.omega = f.omega := by
    rw [hω]
    exact image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hsource (f.omega_subset_source hx)⟩, rfl⟩)
  obtain ⟨a, ha, hUa⟩ := hU
  let ao : O := ⟨a, hsource (f.omega_subset_source ha)⟩
  have hao : ao ∈ g.omega := hω.symm ▸ ha
  refine ⟨ao, hao, ?_⟩
  have he := SurfaceDynamics.embedding_image_connectedComponentIn
    (IsEmbedding.subtypeVal : IsEmbedding (Subtype.val : O → X)) g.omega hao
  rw [him] at he
  rw [hUa, ← he, preimage_image_eq _ Subtype.val_injective]

end SurfaceDynamics.LocalMap
