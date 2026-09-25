/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.BoundaryPunctureSequence
import BoundedWanderingDomains.Surfaces.LocalBarrierComponents
import BoundedWanderingDomains.Surfaces.RestrictedOmega

/-! # Boundary barriers recover restricted normality components -/

open Set Function
open AreaDeficit.Surfaces
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]

/-- The boundary-preimage barrier and the fixed disc cover identify every
complementary component meeting restricted normality with that normality
component. -/
theorem restricted_barrier_component_eq_omega
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (O V : TopologicalSpace.Opens X) (p : DiscCover O)
    (hVsource : (V : Set X) ⊆ f.source)
    (hVcompact : IsCompact (closure (V : Set X)))
    (hVO : closure (V : Set X) ⊆ O) {A : Set X}
    (hA : IsClosed A) (hfront : frontier (V : Set X) ⊆ A)
    (hback : ∀ x : (f.restrictSource V hVsource).source,
      (f.restrictSource V hVsource).map x ∈ A → (x : X) ∈ A)
    (hdis : Disjoint A (f.restrictSource V hVsource).omega)
    {x : X} (hx : x ∈ (f.restrictSource V hVsource).omega) :
    connectedComponentIn Aᶜ x =
      connectedComponentIn (f.restrictSource V hVsource).omega x := by
  letI : LocallyPathConnectedSpace X :=
    ChartedSpace.locallyPathConnectedSpace ℂ X
  let g := f.restrictSource V hVsource
  have hgf : IsOpenHolomorphic g :=
    f.isOpenHolomorphic_restrictSource hf V hVsource
  have homega : g.omega = interior g.trapped :=
    f.omega_restrictSource_eq_interior_trapped hf O V p hVsource
      hVcompact hVO
  exact g.barrier_component_eq_omega_component hgf.2.continuous hA hfront
    hback homega hdis hx

end SurfaceDynamics.LocalMap

#print axioms SurfaceDynamics.LocalMap.restricted_barrier_component_eq_omega
