module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SimplyConnectedCoveringDiscs
public import BoundedWanderingDomains.Surfaces.LocalMapRestriction

@[expose] public section

/-! # Injectivity using regularity only on the visited restriction -/

open Set Function Topology
open scoped Manifold

namespace SurfaceDynamics.LocalMap

theorem injOn_of_simplyConnected_restricted_regular_image
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source)
    {A B : Set X} (hAo : IsOpen A) (hAsc : IsSimplyConnected A)
    (hBo : IsOpen B) (hBsc : IsSimplyConnected B)
    (hAV : A ⊆ V) (hmap : MapsTo f.totalize A B)
    (hreg : B ⊆ (f.restrictSource V hV).regularValues) : InjOn f.totalize A := by
  let g := f.restrictSource V hV
  have heq : EqOn g.totalize f.totalize A := by
    intro x hx
    rw [g.totalize_eq (hAV hx), f.totalize_eq (hV (hAV hx))]
    rfl
  have hi := g.injOn_of_simplyConnected_regular_image
    (f.isOpenHolomorphic_restrictSource hf V hV) hAo hAsc hBo hBsc hAV
    (fun x hx => by rw [heq hx]; exact hmap hx)
    (fun x hx => not_not.mpr (hreg hx))
  intro x hx y hy hxy
  exact hi hx hy ((heq hx).trans (hxy.trans (heq hy).symm))

end SurfaceDynamics.LocalMap
