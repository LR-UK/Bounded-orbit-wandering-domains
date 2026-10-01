module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.Components
public import BoundedWanderingDomains.Surfaces.SingularEncounters.ComponentEmbedding

@[expose] public section

/-! # Open-domain components inside ambient components -/

open Set TopologicalSpace

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem componentDomain_subset_ambientComponent (U : Opens X) (x : U) :
    (componentDomain U (x : X) : Set X) ⊆ ambientComponent (ConnectedComponents.mk (x : X)) := by
  rw [ambientComponent_mk]
  exact isPreconnected_connectedComponentIn.subset_connectedComponent
    (mem_connectedComponentIn x.property)

theorem connectedComponentIn_inter_ambientComponent (c : ConnectedComponents X)
    (U : Opens X) (x : ambientComponent c) (hx : (x : X) ∈ U) :
    connectedComponentIn ((U : Set X) ∩ ambientComponent c) (x : X) =
      connectedComponentIn (U : Set X) (x : X) := by
  apply (connectedComponentIn_mono _ inter_subset_left).antisymm
  apply isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn hx)
  exact subset_inter (connectedComponentIn_subset _ _) (by
    simpa only [componentDomain_coe,
      show ConnectedComponents.mk (x : X) = c from x.property] using
      componentDomain_subset_ambientComponent U ⟨x, hx⟩)

theorem componentPart_componentDomain (c : ConnectedComponents X)
    (U : Opens X) (x : ambientComponent c) (hx : (x : X) ∈ U) :
    componentPart c (componentDomain U (x : X)) =
      componentDomain (componentPart c U) x := by
  have himage : (Subtype.val : ambientComponent c → X) ''
      (componentPart c U : Set (ambientComponent c)) = (U : Set X) ∩ ambientComponent c := by
    ext y
    simp only [mem_image, mem_inter_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz, z.property⟩
    · rintro ⟨hy, hc⟩
      exact ⟨⟨y, hc⟩, hy, rfl⟩
  have he := SurfaceDynamics.embedding_image_connectedComponentIn
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding (Subtype.val : ambientComponent c → X))
    (componentPart c U : Set (ambientComponent c)) hx
  rw [himage, connectedComponentIn_inter_ambientComponent c U x hx] at he
  apply Opens.ext
  change Subtype.val ⁻¹' connectedComponentIn (U : Set X) (x : X) = _
  rw [← he, preimage_image_eq _ Subtype.val_injective]
  rfl

end AreaDeficit.Surfaces
