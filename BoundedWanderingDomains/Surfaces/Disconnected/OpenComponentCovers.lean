module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseLocalCover
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseFilling

@[expose] public section

/-! # Hyperbolizing an open subset separately in its ambient components -/

open Set Function Topology TopologicalSpace
open scoped Manifold

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [SecondCountableTopology X]

theorem nonempty_componentwiseDiscCover_of_component_pieces
    (O : Opens X) (P : ∀ c : ConnectedComponents X, Opens (ambientComponent c))
    (hOP : ∀ c, (Subtype.val : ambientComponent c → X) ⁻¹' (O : Set X) ⊆ P c)
    (hp : ∀ c, ((O : Set X) ∩ ambientComponent c).Nonempty → Nonempty (DiscCover (P c))) :
    Nonempty (ComponentwiseDiscCover O) := by
  classical
  refine ⟨⟨fun d => ?_⟩⟩
  let x : ambientComponent d := Classical.choice (inferInstance : Nonempty (ambientComponent d))
  let c := ConnectedComponents.mk ((x : O) : X)
  let j : ambientComponent d → X := fun y => ((y : O) : X)
  have hj : IsOpenEmbedding j :=
    O.isOpen.isOpenEmbedding_subtypeVal.comp (ambientComponent d).isOpen.isOpenEmbedding_subtypeVal
  have hjh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) j :=
    (mdifferentiable_subtype_val O).comp (mdifferentiable_subtype_val (ambientComponent d))
  have hjc : ∀ y, j y ∈ ambientComponent c := by
    intro y
    change j y ∈ (ambientComponent (ConnectedComponents.mk (j x)) : Set X)
    rw [ambientComponent_mk]
    exact (isPreconnected_range hj.continuous).subset_connectedComponent
      (mem_range_self x) (mem_range_self y)
  let g : ambientComponent d → ambientComponent c := fun y => ⟨j y, hjc y⟩
  let G : ambientComponent d → P c := fun y => ⟨g y, hOP c (y : O).property⟩
  have hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g :=
    (mdifferentiable_subtypeVal_comp_iff (ambientComponent c) g).mp hjh
  have hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G :=
    (mdifferentiable_subtypeVal_comp_iff (P c) G).mp hg
  have hgLoc : IsLocalHomeomorph g :=
    (show IsLocalHomeomorph ((Subtype.val : ambientComponent c → X) ∘ g) from
      hj.isLocalHomeomorph).of_comp
        (ambientComponent c).isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph hg.continuous
  have hGLoc : IsLocalHomeomorph G :=
    (show IsLocalHomeomorph ((Subtype.val : P c → ambientComponent c) ∘ G) from
      hgLoc).of_comp (P c).isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph hG.continuous
  let q := Classical.choice (hp c ⟨j x, (x : O).property, rfl⟩)
  exact Classical.choice (q.nonempty_of_holomorphic_localHomeomorph G hG hGLoc)

omit [IsManifold 𝓘(ℂ) 1 X] [SecondCountableTopology X] in
theorem noncompactComponents_of_omitted_points (O : Opens X)
    (hmiss : ∀ x : O, ∃ y ∈ connectedComponent (x : X), y ∉ O) :
    NoncompactComponents O := by
  let : LocallyConnectedSpace O := ChartedSpace.locallyConnectedSpace ℂ O
  refine ⟨fun x hcompact => ?_⟩
  let C : Set X := (Subtype.val : O → X) '' connectedComponent x
  have hCc : IsClosed C := (hcompact.image continuous_subtype_val).isClosed
  have hCo : IsOpen C := O.isOpen.isOpenMap_subtype_val _ isOpen_connectedComponent
  have hxC : (x : X) ∈ C := ⟨x, mem_connectedComponent, rfl⟩
  obtain ⟨y, hy, hyO⟩ := hmiss x
  obtain ⟨z, _, rfl⟩ := (show IsClopen C from ⟨hCc, hCo⟩).connectedComponent_subset hxC hy
  exact hyO z.property

end AreaDeficit.Surfaces
