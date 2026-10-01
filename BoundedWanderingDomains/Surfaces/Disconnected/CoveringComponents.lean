module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ClopenCovering
public import BoundedWanderingDomains.Surfaces.Disconnected.Components

@[expose] public section

/-! # Coverings restricted to individual source and target components -/

open Set Function Topology

namespace SurfaceDynamics

theorem covering_codRestrict
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} (hc : IsCoveringMap f) (S : Set X) (hS : ∀ x, f x ∈ S) :
    IsCoveringMap (fun x => (⟨f x, hS x⟩ : S)) := by
  have he : f ⁻¹' S = univ := eq_univ_of_forall hS
  let e : E ≃ₜ f ⁻¹' S :=
    (Homeomorph.Set.univ E).symm.trans (Homeomorph.setCongr he).symm
  exact (hc.restrictPreimage S).comp_homeomorph e

end SurfaceDynamics
