/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DerivedLimitReduction

/-! # Component data along a wandering orbit -/

open Set Function OnePoint
open scoped Topology Manifold

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]

/-- The marked orbit of a point in a wandering component lies in the
corresponding pairwise disjoint sequence of normality components. -/
theorem LocalMap.IsWanderingComponent.exists_orbit_components
    (f : LocalMap X) {U : Set X} (hU : f.IsWanderingComponent U)
    {z : X} (hz : z ∈ U) :
    ∃ (V : ℕ → Set X) (hztrapped : z ∈ f.trapped),
      V 0 = U ∧
      (∀ n, f.IsComponent (V n)) ∧
      (∀ n, f.orbit n ⟨z, hztrapped⟩ ∈ V n) ∧
      Pairwise (fun n m => Disjoint (V n) (V m)) := by
  have hztrapped : z ∈ f.trapped :=
    LocalMap.IsWanderingComponent.subset_trapped f hU hz
  obtain ⟨V, hV0, hcomp, himage, hdis⟩ := hU
  refine ⟨V, hztrapped, hV0, hcomp, ?_, hdis⟩
  intro n
  apply himage n
  exact ⟨z, hz, f.iterate_eq_some_orbit n ⟨z, hztrapped⟩⟩

/-- Compact containment of the compactified marked orbit is the same as
compact containment of its genuine trapped orbit. -/
theorem LocalMap.orbit_mem_of_compactifiedIterate_mem_image
    (f : LocalMap X) {z : X} (hz : z ∈ f.trapped) {K : Set X}
    (hK : ∀ n, f.compactifiedIterate n z ∈ ((↑) : X → OnePoint X) '' K) :
    ∀ n, f.orbit n ⟨z, hz⟩ ∈ K := by
  intro n
  obtain ⟨w, hwK, hw⟩ := hK n
  rw [f.compactifiedIterate_eq_orbit n ⟨z, hz⟩] at hw
  exact OnePoint.coe_injective hw ▸ hwK

end SurfaceDynamics

#print axioms SurfaceDynamics.LocalMap.IsWanderingComponent.exists_orbit_components
#print axioms SurfaceDynamics.LocalMap.orbit_mem_of_compactifiedIterate_mem_image
