/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.ChartPullbackExtension
import BoundedWanderingDomains.Surfaces.CoordinateDiskSelection
import BoundedWanderingDomains.LogarithmicCutoff

/-! # Logarithmic cutoffs in surface charts -/

open Set Function Filter Metric
open scoped Manifold Topology ContDiff

namespace AreaDeficit.Surfaces

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M]

/-- The planar logarithmic cutoff at the centre of a coordinate disc,
pulled back to the surface and extended by zero outside the chart. -/
noncomputable def surfaceLogCutoff
    (D : RiemannDynamics.CoordDisk M) (t : ℝ) : M → ℝ :=
  chartPullbackExtension (chartAt ℂ D.center)
    (AreaDeficit.logCutoff (chartAt ℂ D.center D.center) (-2 * t) (-t))

theorem exp_neg_le_coordDisk_radius
    (D : RiemannDynamics.CoordDisk M) {t : ℝ}
    (ht : -Real.log D.radius ≤ t) :
    Real.exp (-t) ≤ D.radius := by
  rw [← Real.exp_log D.radius_pos]
  exact Real.exp_le_exp.mpr (by linarith)

theorem surfaceLogCutoff_planar_tsupport_subset
    (D : RiemannDynamics.CoordDisk M) {t : ℝ} (ht : 0 < t)
    (hr : -Real.log D.radius ≤ t) :
    tsupport (AreaDeficit.logCutoff
      (chartAt ℂ D.center D.center) (-2 * t) (-t)) ⊆
        (chartAt ℂ D.center).target := by
  refine (AreaDeficit.logCutoff_tsupport (by linarith)).trans ?_
  exact (closedBall_subset_closedBall
    (exp_neg_le_coordDisk_radius D hr)).trans D.closedBall_subset

theorem surfaceLogCutoff_contMDiff
    (D : RiemannDynamics.CoordDisk M) {t : ℝ} (ht : 0 < t)
    (hr : -Real.log D.radius ≤ t) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 (surfaceLogCutoff D t) := by
  apply contMDiff_chartPullbackExtension
  · exact (AreaDeficit.logCutoff_contDiff _ (by linarith)).of_le (by norm_num)
  · exact AreaDeficit.logCutoff_hasCompactSupport _ (by linarith)
  · exact surfaceLogCutoff_planar_tsupport_subset D ht hr
  · letI : IsManifold 𝓘(ℝ, ℂ) ∞ M := isManifold_real_of_complex
    exact (contDiffGroupoid 2 𝓘(ℝ, ℂ)).chart_mem_maximalAtlas D.center

theorem surfaceLogCutoff_hasCompactSupport
    (D : RiemannDynamics.CoordDisk M) {t : ℝ} (ht : 0 < t)
    (hr : -Real.log D.radius ≤ t) :
    HasCompactSupport (surfaceLogCutoff D t) := by
  apply hasCompactSupport_chartPullbackExtension
  · exact AreaDeficit.logCutoff_hasCompactSupport _ (by linarith)
  · exact surfaceLogCutoff_planar_tsupport_subset D ht hr

theorem surfaceLogCutoff_tsupport_subset_closedCarrier
    (D : RiemannDynamics.CoordDisk M) {t : ℝ} (ht : 0 < t)
    (hr : -Real.log D.radius ≤ t) :
    tsupport (surfaceLogCutoff D t) ⊆ D.closedCarrier := by
  apply closure_minimal _ D.isCompact_closedCarrier.isClosed
  refine support_chartPullbackExtension_subset.trans ?_
  rintro x ⟨z, hz, rfl⟩
  refine ⟨z, ?_, rfl⟩
  exact closedBall_subset_closedBall (exp_neg_le_coordDisk_radius D hr)
    ((AreaDeficit.logCutoff_tsupport (by linarith)) (subset_closure hz))

theorem surfaceLogCutoff_bounds
    (D : RiemannDynamics.CoordDisk M) (t : ℝ) (x : M) :
    0 ≤ surfaceLogCutoff D t x ∧ surfaceLogCutoff D t x ≤ 1 := by
  by_cases hx : x ∈ (chartAt ℂ D.center).source
  · rw [surfaceLogCutoff, chartPullbackExtension_eq hx]
    exact AreaDeficit.logCutoff_bounds _ _ _ _
  · simp [surfaceLogCutoff, chartPullbackExtension, hx]

theorem surfaceLogCutoff_eq_one
    (D : RiemannDynamics.CoordDisk M) {t : ℝ} (ht : 0 < t)
    {x : M} (hx : x ∈ (chartAt ℂ D.center).source)
    (hdist : ‖chartAt ℂ D.center x - chartAt ℂ D.center D.center‖ ≤
      Real.exp (-2 * t)) :
    surfaceLogCutoff D t x = 1 := by
  rw [surfaceLogCutoff, chartPullbackExtension_eq hx]
  exact AreaDeficit.logCutoff_eq_one (by linarith) hdist

theorem surfaceLogCutoff_eq_zero
    (D : RiemannDynamics.CoordDisk M) {t : ℝ} (ht : 0 < t)
    {x : M} (hx : x ∈ (chartAt ℂ D.center).source)
    (hdist : Real.exp (-t) ≤
      ‖chartAt ℂ D.center x - chartAt ℂ D.center D.center‖) :
    surfaceLogCutoff D t x = 0 := by
  rw [surfaceLogCutoff, chartPullbackExtension_eq hx]
  exact AreaDeficit.logCutoff_eq_zero (by linarith) hdist

theorem surfaceLogCutoff_center
    (D : RiemannDynamics.CoordDisk M) {t : ℝ} (ht : 0 < t) :
    surfaceLogCutoff D t D.center = 1 := by
  apply surfaceLogCutoff_eq_one D ht (mem_chart_source ℂ D.center)
  simpa using (Real.exp_pos (-(2 * t))).le

theorem surfaceLogCutoff_eventually_zero
    (D : RiemannDynamics.CoordDisk M) {x : M} (hx : x ≠ D.center) :
    ∀ᶠ t : ℝ in atTop, surfaceLogCutoff D t x = 0 := by
  by_cases hxs : x ∈ (chartAt ℂ D.center).source
  · have hcs : D.center ∈ (chartAt ℂ D.center).source :=
      mem_chart_source ℂ D.center
    have hcoord : chartAt ℂ D.center x ≠ chartAt ℂ D.center D.center := by
      intro h
      apply hx
      calc
        x = (chartAt ℂ D.center).symm (chartAt ℂ D.center x) :=
          ((chartAt ℂ D.center).left_inv hxs).symm
        _ = (chartAt ℂ D.center).symm
            (chartAt ℂ D.center D.center) := congrArg _ h
        _ = D.center := (chartAt ℂ D.center).left_inv hcs
    have hlim : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      hlim.eventually (eventually_lt_nhds
        (norm_pos_iff.mpr (sub_ne_zero.mpr hcoord)))] with t ht hdist
    exact surfaceLogCutoff_eq_zero D ht hxs hdist.le
  · exact Eventually.of_forall fun t => by
      simp [surfaceLogCutoff, chartPullbackExtension, hxs]

end AreaDeficit.Surfaces

#print axioms AreaDeficit.Surfaces.surfaceLogCutoff_contMDiff
