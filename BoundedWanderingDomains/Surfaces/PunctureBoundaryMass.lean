/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.LogGrowthCutoff
import BoundedWanderingDomains.Surfaces.PunctureLogRatioBound

/-! # Uniform boundary mass at a newly inserted surface puncture -/

open Set Function Filter Metric MeasureTheory Laplacian
open scoped Manifold Topology

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

/-- The log-density ratio at one newly inserted puncture has a uniformly
bounded Riesz boundary contribution.  This is the direct formal version of
the new-puncture part of Lemma 2.6. -/
theorem eventually_bounded_new_puncture_boundary_mass
    (p : DiscCover M) {U : TopologicalSpace.Opens M} (q : DiscCover U)
    (hU : Nonempty U) {d : OpenPartialHomeomorph M ℂ}
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {a : ℂ} (ha : a ∈ d.target) {R : ℝ} (hR : 0 < R)
    (hball : ball a R \ {a} ⊆ (d.subtypeRestr hU).target) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ t : ℝ in atTop,
      |∫ z : ℂ, p.chartLogRatio q hU d z *
        Δ (AreaDeficit.logCutoff a (-2 * t) (-t)) z| ≤ B := by
  obtain ⟨r, hr, hrR, C, hC, hgrowth⟩ :=
    p.exists_chartLogRatio_le_const_sub_log_norm q hU hd ha hR hball
  let H : ℝ := 2 * Real.pi * ∫ s : ℝ, |AreaDeficit.transitionSecond s|
  have hH : 0 ≤ H := by dsimp [H]; positivity
  let B : ℝ := C * H + 2 * H
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  filter_upwards [eventually_gt_atTop (-Real.log r),
    eventually_gt_atTop (1 : ℝ)] with t htr ht1
  have ht : 0 < t := lt_trans zero_lt_one ht1
  have hmain := AreaDeficit.integral_mul_laplacian_logCutoff_neg_two_neg_one_le
    (f := p.chartLogRatio q hU d) a ht hC (by norm_num : (0 : ℝ) ≤ 1)
      (fun z hza _ hzB => by
        have hn : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hza)
        have hzr : ‖z - a‖ < r :=
          (Real.log_lt_log_iff hn hr).mp (hzB.trans (by linarith))
        have hzR : ‖z - a‖ < R := hzr.trans hrR
        have hzt : z ∈ (d.subtypeRestr hU).target :=
          hball ⟨by simpa only [mem_ball, dist_eq_norm] using hzR,
            by simpa only [mem_singleton_iff] using hza⟩
        have hnonneg := p.chartLogRatio_nonneg q hU hd hzt
        have hupper := hgrowth z hza hzr
        rw [abs_of_nonneg hnonneg, abs_of_neg (hzB.trans (by linarith))]
        linarith)
  have hHt : H / t ≤ H := div_le_self hH (by linarith)
  calc
    |∫ z : ℂ, p.chartLogRatio q hU d z *
        Δ (AreaDeficit.logCutoff a (-2 * t) (-t)) z| ≤
        C * (H / t) + 2 * H := by
          convert hmain using 1 <;> simp only [H] <;> ring
    _ ≤ C * H + 2 * H := by
      gcongr
    _ = B := rfl

end AreaDeficit.Surfaces.DiscCover

#print axioms AreaDeficit.Surfaces.DiscCover.eventually_bounded_new_puncture_boundary_mass
