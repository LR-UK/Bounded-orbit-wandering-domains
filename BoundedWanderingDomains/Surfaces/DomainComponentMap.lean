module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.DomainCoveringPullback

@[expose] public section

/-! # Maps induced between connected components of open domains -/

open Set Function
open scoped Manifold

namespace AreaDeficit.Surfaces

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [TopologicalSpace N] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ) 1 N]

/-- A continuous map between open domains sends the connected component of
a point into the connected component of its image. -/
noncomputable def domainComponentMap
    {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens N}
    (F : U → V) (hF : Continuous F) (x : U) :
    componentDomain U (x : M) → componentDomain V (F x : N) := by
  let C := componentDomain U (x : M)
  letI : ConnectedSpace C := componentDomain_connected x.property
  let iC : C → U := fun z => ⟨z, componentDomain_le U (x : M) z.property⟩
  let fv : C → N := (Subtype.val : V → N) ∘ F ∘ iC
  have hfv : Continuous fv := continuous_subtype_val.comp (hF.comp (by fun_prop))
  have hrange : range fv ⊆ connectedComponentIn V (F x : N) := by
    apply (isPreconnected_range hfv).subset_connectedComponentIn
    · exact ⟨⟨x, mem_componentDomain x.property⟩, rfl⟩
    · rintro _ ⟨z, rfl⟩
      exact (F (iC z)).property
  exact fun z => ⟨fv z, hrange (mem_range_self z)⟩

omit [IsManifold 𝓘(ℂ, ℂ) 1 M] [IsManifold 𝓘(ℂ, ℂ) 1 N] in
@[simp] theorem domainComponentMap_coe
    {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens N}
    (F : U → V) (hF : Continuous F) (x : U)
    (z : componentDomain U (x : M)) :
    (domainComponentMap F hF x z : N) = F ⟨z, componentDomain_le U (x : M) z.property⟩ := rfl

omit [IsManifold 𝓘(ℂ, ℂ) 1 M] [IsManifold 𝓘(ℂ, ℂ) 1 N] in
theorem domainComponentMap_mdifferentiable
    {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens N}
    (F : U → V) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (x : U) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (domainComponentMap F hF.continuous x) := by
  let C := componentDomain U (x : M)
  let D := componentDomain V (F x : N)
  let iC : C → U := fun z => ⟨z, componentDomain_le U (x : M) z.property⟩
  have hiC : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) iC := by
    apply (mdifferentiable_subtypeVal_comp_iff U iC).mp
    have he : (Subtype.val ∘ iC : C → M) = (Subtype.val : C → M) := by
      funext z
      rfl
    rw [he]
    exact mdifferentiable_subtype_val C
  apply (mdifferentiable_subtypeVal_comp_iff D
    (domainComponentMap F hF.continuous x)).mp
  have he : (Subtype.val ∘ domainComponentMap F hF.continuous x : C → N) =
      (Subtype.val : V → N) ∘ F ∘ iC := by
    funext z
    rfl
  rw [he]
  exact (mdifferentiable_subtype_val V).comp (hF.comp hiC)

omit [IsManifold 𝓘(ℂ, ℂ) 1 M] [IsManifold 𝓘(ℂ, ℂ) 1 N] in
@[simp] theorem domainComponentMap_componentPoint
    {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens N}
    (F : U → V) (hF : Continuous F) (x : U) :
    domainComponentMap F hF x (DiscCover.componentPoint U x) =
      DiscCover.componentPoint V ⟨F x, (F x).property⟩ := Subtype.ext rfl

end AreaDeficit.Surfaces
