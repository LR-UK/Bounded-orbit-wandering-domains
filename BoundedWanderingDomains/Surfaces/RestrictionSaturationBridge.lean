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

/-- When the old saturation remains in the smaller source, source
restriction does not change that saturation. -/
theorem restrictSource_saturation_eq_of_saturation_subset
    (f : LocalMap X) (V : TopologicalSpace.Opens X)
    (hV : (V : Set X) ⊆ f.source) {A : Set X}
    (hAtrap : A ⊆ f.trapped) (hsat : f.saturation A ⊆ V) :
    (f.restrictSource V hV).saturation A = f.saturation A := by
  have hArestrict : A ⊆ (f.restrictSource V hV).trapped := by
    intro x hx
    exact f.restrictSource_mem_trapped_of_orbit_mem V hV (hAtrap hx)
      (fun n => hsat (mem_iUnion.mpr
        ⟨n, x, hx, f.iterate_eq_some_orbit n ⟨x, hAtrap hx⟩⟩))
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨n, x, hx, hxy⟩ := mem_iUnion.mp hy
    apply mem_iUnion.mpr
    refine ⟨n, x, hx, ?_⟩
    rw [← f.restrictSource_iterate_eq_of_restricted_trapped V hV
      (hArestrict hx) n]
    exact hxy
  · intro y hy
    obtain ⟨n, x, hx, hxy⟩ := mem_iUnion.mp hy
    apply mem_iUnion.mpr
    refine ⟨n, x, hx, ?_⟩
    rw [f.restrictSource_iterate_eq_of_restricted_trapped V hV
      (hArestrict hx) n]
    exact hxy

/-- Each finite image is unchanged when the whole saturation stays in the
smaller source. -/
theorem restrictSource_imageAt_eq_of_saturation_subset
    (f : LocalMap X) (V : TopologicalSpace.Opens X)
    (hV : (V : Set X) ⊆ f.source) {A : Set X}
    (hAtrap : A ⊆ f.trapped) (hsat : f.saturation A ⊆ V) (n : ℕ) :
    (f.restrictSource V hV).imageAt n A = f.imageAt n A := by
  have hArestrict : A ⊆ (f.restrictSource V hV).trapped := by
    intro x hx
    exact f.restrictSource_mem_trapped_of_orbit_mem V hV (hAtrap hx)
      (fun k => hsat (mem_iUnion.mpr
        ⟨k, x, hx, f.iterate_eq_some_orbit k ⟨x, hAtrap hx⟩⟩))
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    rw [← f.restrictSource_iterate_eq_of_restricted_trapped V hV
      (hArestrict hx) n]
    exact hxy
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    rw [f.restrictSource_iterate_eq_of_restricted_trapped V hV
      (hArestrict hx) n]
    exact hxy

/-- Injectivity on a saturation is preserved by a source restriction which
contains that saturation. -/
theorem injectiveOnSaturation_restrictSource
    (f : LocalMap X) (V : TopologicalSpace.Opens X)
    (hV : (V : Set X) ⊆ f.source) {A : Set X}
    (hAtrap : A ⊆ f.trapped) (hsat : f.saturation A ⊆ V)
    (hinj : f.InjectiveOnSaturation A) :
    (f.restrictSource V hV).InjectiveOnSaturation A := by
  have hsateq := f.restrictSource_saturation_eq_of_saturation_subset
    V hV hAtrap hsat
  intro x hx y hy hxy
  have hxy' : f.map ⟨(x : X), hV x.property⟩ =
      f.map ⟨(y : X), hV y.property⟩ := hxy
  have he := hinj (hsateq ▸ hx) (hsateq ▸ hy) hxy'
  apply Subtype.ext
  exact congrArg (fun z : f.source => (z : X)) he

end SurfaceDynamics.LocalMap

#print axioms SurfaceDynamics.LocalMap.subset_restrictSource_trapped_diff_omega_of_saturation_subset
#print axioms SurfaceDynamics.LocalMap.restrictSource_saturation_eq_of_saturation_subset
#print axioms SurfaceDynamics.LocalMap.restrictSource_imageAt_eq_of_saturation_subset
#print axioms SurfaceDynamics.LocalMap.injectiveOnSaturation_restrictSource
