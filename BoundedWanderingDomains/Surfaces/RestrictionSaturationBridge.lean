/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.LocalMapRestriction
import BoundedWanderingDomains.Surfaces.SaturationDynamics

/-! # Forward saturations after restricting a local map -/

open Set Function
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]

/-- If the whole forward saturation of `A` lies in a smaller source, then
every point of `A` is trapped for the restricted map.  Points outside the
old normality locus remain outside the restricted normality locus. -/
theorem subset_restrictSource_trapped_diff_omega_of_saturation_subset
    (f : LocalMap X) (V : TopologicalSpace.Opens X)
    (hV : (V : Set X) ⊆ f.source) {A : Set X}
    (hA : A ⊆ f.trapped \ f.omega) (hsat : f.saturation A ⊆ V) :
    A ⊆ (f.restrictSource V hV).trapped \ (f.restrictSource V hV).omega := by
  intro x hx
  have hxtrap : x ∈ f.trapped := (hA hx).1
  have hstay : ∀ n, f.orbit n ⟨x, hxtrap⟩ ∈ V := by
    intro n
    apply hsat
    apply mem_iUnion.mpr
    exact ⟨n, x, hx, f.iterate_eq_some_orbit n ⟨x, hxtrap⟩⟩
  refine ⟨f.restrictSource_mem_trapped_of_orbit_mem V hV hxtrap hstay, ?_⟩
  intro homega
  exact (hA hx).2 (f.restrictSource_omega_subset V hV homega)

end SurfaceDynamics.LocalMap

#print axioms SurfaceDynamics.LocalMap.subset_restrictSource_trapped_diff_omega_of_saturation_subset
