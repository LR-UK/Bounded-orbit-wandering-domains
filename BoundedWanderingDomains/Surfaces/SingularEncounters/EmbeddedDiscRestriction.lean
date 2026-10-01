module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.FullRestrictionComponents

@[expose] public section

open Set Function Topology
open AreaDeficit.Surfaces
open scoped Manifold

namespace SurfaceDynamics.EmbeddedDisc

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

def restrict (Q : EmbeddedDisc X) (O : TopologicalSpace.Opens X)
    (hQO : (Q.carrier : Set X) ⊆ O) : EmbeddedDisc O where
  param := fun w => ⟨Q.param w, hQO (mem_range_self w)⟩
  holomorphic := (mdifferentiable_subtypeVal_comp_iff O _).mp Q.holomorphic
  embedding := O.isOpen.isOpenEmbedding_subtypeVal.of_comp _ Q.embedding

theorem restrict_carrier (Q : EmbeddedDisc X) (O : TopologicalSpace.Opens X)
    (hQO : (Q.carrier : Set X) ⊆ O) :
    ((Q.restrict O hQO).carrier : Set O) = Subtype.val ⁻¹' (Q.carrier : Set X) := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact mem_range_self w
  · rintro ⟨w, hw⟩
    exact ⟨w, Subtype.ext hw⟩

theorem ambientOpen_restrict_carrier (Q : EmbeddedDisc X) (O : TopologicalSpace.Opens X)
    (hQO : (Q.carrier : Set X) ⊆ O) :
    ambientOpen O (Q.restrict O hQO).carrier = Q.carrier := by
  apply TopologicalSpace.Opens.ext
  change Subtype.val '' ((Q.restrict O hQO).carrier : Set O) = (Q.carrier : Set X)
  rw [Q.restrict_carrier]
  exact image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hQO hx⟩, rfl⟩)

end SurfaceDynamics.EmbeddedDisc
