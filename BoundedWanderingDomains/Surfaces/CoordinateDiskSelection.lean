/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.OpenMapping
import BoundedWanderingDomains.Surfaces.UniformizationBridge

/-! # Selecting a coordinate disk inside an open surface set -/

open Set Function Metric
open scoped Manifold Topology

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-- Every point of a nonempty open surface set has another point beside it. -/
theorem exists_mem_ne_of_isOpen_surface {U : Set X} (hU : IsOpen U) {z : X}
    (hz : z ∈ U) : ∃ w ∈ U, w ≠ z := by
  by_contra h
  push_neg at h
  have hUz : U = ({z} : Set X) := by
    apply Set.Subset.antisymm
    · intro w hw
      exact Set.mem_singleton_iff.mpr (h w hw)
    · exact Set.singleton_subset_iff.mpr hz
  exact not_isOpen_singleton_surface z (hUz ▸ hU)

/-- Inside an open set, choose a closed coordinate disk avoiding one
prescribed point. -/
theorem exists_coordDisk_closedCarrier_subset_diff {U : Set X}
    (hU : IsOpen U) {z : X} (hz : z ∈ U) :
    ∃ D : RiemannDynamics.CoordDisk X, D.closedCarrier ⊆ U \ {z} := by
  obtain ⟨w, hwU, hwz⟩ := exists_mem_ne_of_isOpen_surface hU hz
  let e := chartAt ℂ w
  have hdiff : IsOpen (U \ ({z} : Set X)) := hU.sdiff isClosed_singleton
  have hopen : IsOpen (e.target ∩ e.symm ⁻¹' (U \ ({z} : Set X))) :=
    e.isOpen_inter_preimage_symm hdiff
  have hwsource : w ∈ e.source := mem_chart_source ℂ w
  have hwmem : e w ∈ e.target ∩ e.symm ⁻¹' (U \ ({z} : Set X)) := by
    refine ⟨e.map_source hwsource, ?_⟩
    rw [Set.mem_preimage, e.left_inv hwsource]
    exact ⟨hwU, hwz⟩
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hopen (e w) hwmem
  have hr2 : 0 < r / 2 := by linarith
  have hclosed : closedBall (e w) (r / 2) ⊆
      e.target ∩ e.symm ⁻¹' (U \ ({z} : Set X)) :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrsub
  let D : RiemannDynamics.CoordDisk X :=
    ⟨w, r / 2, hr2, fun y hy => (hclosed hy).1⟩
  refine ⟨D, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  exact (hclosed hy).2

end SurfaceDynamics

#print axioms SurfaceDynamics.exists_coordDisk_closedCarrier_subset_diff
