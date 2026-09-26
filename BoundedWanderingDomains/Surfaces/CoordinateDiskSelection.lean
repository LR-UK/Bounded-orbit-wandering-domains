/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.OpenMapping
import BoundedWanderingDomains.Surfaces.UniformizationBridge

/-! # Selecting a coordinate disk inside an open surface set -/

open Set Function Metric
open scoped Manifold Topology ContDiff

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

/-- A prescribed point has a closed coordinate disk centred at that point
and contained in any given open neighbourhood. -/
theorem exists_coordDisk_center_closedCarrier_subset {U : Set X}
    (hU : IsOpen U) {z : X} (hz : z ∈ U) :
    ∃ D : RiemannDynamics.CoordDisk X,
      D.center = z ∧ D.closedCarrier ⊆ U := by
  let e := chartAt ℂ z
  have hopen : IsOpen (e.target ∩ e.symm ⁻¹' U) :=
    e.isOpen_inter_preimage_symm hU
  have hzsource : z ∈ e.source := mem_chart_source ℂ z
  have hzmem : e z ∈ e.target ∩ e.symm ⁻¹' U := by
    refine ⟨e.map_source hzsource, ?_⟩
    rw [Set.mem_preimage, e.left_inv hzsource]
    exact hz
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hopen (e z) hzmem
  have hr2 : 0 < r / 2 := by linarith
  have hclosed : closedBall (e z) (r / 2) ⊆ e.target ∩ e.symm ⁻¹' U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrsub
  let D : RiemannDynamics.CoordDisk X :=
    ⟨z, r / 2, hr2, fun y hy => (hclosed hy).1⟩
  refine ⟨D, rfl, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  exact (hclosed hy).2

/-- Every proper closed set is contained in a fixed disc-covered open
subsurface.  The deleted coordinate disk can be chosen wholly in its
complement. -/
theorem exists_discCovered_coordDisk_compl_of_isClosed
    [SecondCountableTopology X] [ConnectedSpace X]
    {K : Set X} (hK : IsClosed K)
    (hKne : K ≠ Set.univ) :
    ∃ (D : RiemannDynamics.CoordDisk X)
      (p : AreaDeficit.Surfaces.DiscCover D.compl),
      K ⊆ (D.compl : Set X) := by
  obtain ⟨x, hx⟩ : ∃ x : X, x ∉ K := by
    by_contra h
    push Not at h
    exact hKne (eq_univ_iff_forall.mpr h)
  obtain ⟨D, hDcenter, hD⟩ :=
    exists_coordDisk_center_closedCarrier_subset hK.isOpen_compl hx
  letI : IsManifold 𝓘(ℂ) ω X :=
    AreaDeficit.Surfaces.isManifold_analytic_of_complex
  let p : AreaDeficit.Surfaces.DiscCover D.compl :=
    Classical.choice
      (AreaDeficit.Surfaces.nonempty_discCover_coordDisk_compl D)
  refine ⟨D, p, ?_⟩
  intro y hyK hyD
  exact (hD hyD) hyK

end SurfaceDynamics

#print axioms SurfaceDynamics.exists_coordDisk_closedCarrier_subset_diff
#print axioms SurfaceDynamics.exists_coordDisk_center_closedCarrier_subset
#print axioms SurfaceDynamics.exists_discCovered_coordDisk_compl_of_isClosed
