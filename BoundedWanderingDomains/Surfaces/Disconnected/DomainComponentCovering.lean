module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.CoveringComponents
public import BoundedWanderingDomains.Surfaces.Disconnected.OpenComponents
public import BoundedWanderingDomains.Surfaces.SubtypeHolomorphic

@[expose] public section

/-! # Every source component of a covering maps to one target component -/

open Set Function Topology TopologicalSpace
open AreaDeficit.Surfaces
open scoped Manifold

namespace SurfaceDynamics

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) 1 N]

omit [IsManifold 𝓘(ℂ) 1 M] in
theorem covering_domainComponent (U : Opens M) (V : Opens N)
    (F : U → V) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hc : IsCoveringMap F)
    (c : ConnectedComponents U) :
    ∃ (d : ConnectedComponents V) (G : domainComponent U c → domainComponent V d),
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ IsCoveringMap G ∧
      ∀ x, (G x : N) = (F ⟨x, domainComponent_le U c x.property⟩ : N) := by
  classical
  let a : ambientComponent c := Classical.choice (inferInstance : Nonempty (ambientComponent c))
  let H : ambientComponent c → V := fun x => F x
  let d := ConnectedComponents.mk (H a)
  have hHd : ∀ x, H x ∈ ambientComponent d := by
    intro x
    change H x ∈ (ambientComponent d : Set V)
    rw [show (ambientComponent d : Set V) = connectedComponent (H a) from ambientComponent_mk (H a)]
    exact (isPreconnected_range (hc.continuous.comp continuous_subtype_val)).subset_connectedComponent
      (mem_range_self a) (mem_range_self x)
  have hHc : IsCoveringMap H := covering_clopen_source hc
    ⟨(isClosed_ambientComponent c), (ambientComponent c).isOpen⟩
  let H' : ambientComponent c → ambientComponent d := fun x => ⟨H x, hHd x⟩
  have hH'c : IsCoveringMap H' := covering_codRestrict hHc _ hHd
  let eC := domainComponentHomeomorph U c
  let eD := domainComponentHomeomorph V d
  let G := eD ∘ H' ∘ eC.symm
  have hagrees : ∀ x, (G x : N) = (F ⟨x, domainComponent_le U c x.property⟩ : N) := by
    intro x
    change (F ((eC.symm x : ambientComponent c) : U) : N) = _
    have he : (((eC.symm x : ambientComponent c) : U) : M) = (x : M) :=
      congrArg (fun y : domainComponent U c => (y : M)) (eC.apply_symm_apply x)
    exact congrArg (fun y : U => (F y : N)) (Subtype.ext he)
  refine ⟨d, G, ?_, (hH'c.comp_homeomorph eC.symm).homeomorph_comp eD, hagrees⟩
  apply (mdifferentiable_subtypeVal_comp_iff (domainComponent V d) G).mp
  have he : (Subtype.val : domainComponent V d → N) ∘ G =
      (Subtype.val : V → N) ∘ F ∘ Set.inclusion (domainComponent_le U c) := funext hagrees
  rw [he]
  apply (mdifferentiable_subtype_val V).comp (hF.comp ?_)
  apply (mdifferentiable_subtypeVal_comp_iff U _).mp
  exact mdifferentiable_subtype_val (domainComponent U c)

end SurfaceDynamics
