module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentDomains

@[expose] public section

/-! # The components of an open domain as open subsets of the ambient manifold -/

open Set Function TopologicalSpace

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

def domainComponent (U : Opens X) (c : ConnectedComponents U) : Opens X :=
  ⟨Subtype.val '' (ambientComponent c : Set U),
    U.isOpen.isOpenMap_subtype_val _ (ambientComponent c).isOpen⟩

theorem domainComponent_le (U : Opens X) (c : ConnectedComponents U) :
    domainComponent U c ≤ U := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

theorem domainComponent_mk (U : Opens X) (x : U) :
    domainComponent U (ConnectedComponents.mk x) = componentDomain U (x : X) := by
  apply Opens.ext
  change Subtype.val '' (ambientComponent (ConnectedComponents.mk x) : Set U) = _
  rw [ambientComponent_mk, componentDomain_coe, connectedComponentIn_eq_image x.property]
  rfl

instance domainComponent_connectedSpace (U : Opens X) (c : ConnectedComponents U) :
    ConnectedSpace (domainComponent U c) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [domainComponent_mk]
  exact componentDomain_connected x.property

theorem domainComponent_pairwise_disjoint (U : Opens X) :
    Pairwise (fun c d : ConnectedComponents U =>
      Disjoint (domainComponent U c : Set X) (domainComponent U d : Set X)) := by
  intro c d hcd
  exact (ambientComponent_pairwise_disjoint hcd).image Subtype.val_injective.injOn
    (subset_univ _) (subset_univ _)

theorem iUnion_domainComponent (U : Opens X) :
    (⋃ c : ConnectedComponents U, (domainComponent U c : Set X)) = U := by
  change (⋃ c : ConnectedComponents U, Subtype.val '' (ambientComponent c : Set U)) = _
  rw [← image_iUnion, iUnion_ambientComponent, image_univ, Subtype.range_coe]

noncomputable def domainComponentHomeomorph (U : Opens X) (c : ConnectedComponents U) :
    ambientComponent c ≃ₜ domainComponent U c :=
  U.isOpen.isOpenEmbedding_subtypeVal.isEmbedding.homeomorphImage (ambientComponent c : Set U)

@[simp] theorem domainComponentHomeomorph_apply (U : Opens X)
    (c : ConnectedComponents U) (x : ambientComponent c) :
    (domainComponentHomeomorph U c x : X) = ((x : U) : X) := rfl

end AreaDeficit.Surfaces
