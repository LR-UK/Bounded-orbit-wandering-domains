/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.SubdomainCover
import BoundedWanderingDomains.Surfaces.ComponentDomains
import BoundedWanderingDomains.Surfaces.KernelDomains

/-! # Intrinsic density on possibly disconnected open subdomains

Each point uses the disc cover of its actual connected component. Cover
independence identifies this with any supplied cover of that component.
-/
open Set Function
open scoped Manifold
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

theorem density_eq_of_domain_eq
    {U V : TopologicalSpace.Opens M} (hUV : U = V)
    (p : DiscCover U) (q : DiscCover V) (hU : Nonempty U) (hV : Nonempty V)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {x : M} (hxU : x ∈ U) (hxV : x ∈ V) (hxc : x ∈ c.source) :
    p.density (c.subtypeRestr hU) ⟨x,hxU⟩ =
      q.density (c.subtypeRestr hV) ⟨x,hxV⟩ := by
  subst V
  apply p.density_independent q (mdifferentiableOn_subtypeRestr hU hc)
  simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hxc

variable [T2Space M] [SecondCountableTopology M]

noncomputable def componentCover (p : DiscCover M)
    (U : TopologicalSpace.Opens M) (x : U) : DiscCover (componentDomain U (x : M)) := by
  let : ConnectedSpace (componentDomain U (x : M)) := componentDomain_connected x.property
  exact Classical.choice (p.nonempty_subdomain (componentDomain U (x : M)))

def componentPoint (U : TopologicalSpace.Opens M) (x : U) : componentDomain U (x : M) :=
  ⟨(x : M), mem_componentDomain x.property⟩

noncomputable def domainDensity (p : DiscCover M) (U : TopologicalSpace.Opens M)
    (c : OpenPartialHomeomorph M ℂ) (x : U) : ℝ :=
  (p.componentCover U x).density (c.subtypeRestr ⟨componentPoint U x⟩) (componentPoint U x)

theorem domainDensity_pos (p : DiscCover M) (U : TopologicalSpace.Opens M)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {x : U} (hx : (x : M) ∈ c.source) : 0 < p.domainDensity U c x := by
  apply (p.componentCover U x).density_pos
    (mdifferentiableOn_subtypeRestr ⟨componentPoint U x⟩ hc)
  simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage, componentPoint] using hx

/-- On a fixed component, the componentwise density agrees with any
chosen cover of that component, not merely the cover chosen at the point. -/
theorem domainDensity_eq_on_component (p : DiscCover M) (U : TopologicalSpace.Opens M)
    (x y : U) (hy : (y : M) ∈ componentDomain U (x : M))
    (q : DiscCover (componentDomain U (x : M)))
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hyc : (y : M) ∈ c.source) :
    p.domainDensity U c y = q.density
      (c.subtypeRestr ⟨componentPoint U x⟩) ⟨(y : M),hy⟩ := by
  exact density_eq_of_domain_eq (componentDomain_eq_of_mem hy)
    (p.componentCover U y) q ⟨componentPoint U y⟩ ⟨componentPoint U x⟩
    hc (mem_componentDomain y.property) hy hyc

end AreaDeficit.Surfaces.DiscCover
