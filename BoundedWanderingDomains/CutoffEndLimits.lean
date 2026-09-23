/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.CutoffError
import BoundedWanderingDomains.CuspEndLimits

open Set Filter MeasureTheory InnerProductSpace Laplacian Metric
open scoped Topology ContDiff

namespace AreaDeficit

theorem logCutoff_laplacian_tsupport {a : ℂ} {A B : ℝ} (hAB : A < B) :
    tsupport (Δ (logCutoff a A B)) ⊆
      {z : ℂ | Real.exp A ≤ ‖z - a‖ ∧ ‖z - a‖ ≤ Real.exp B} := by
  apply closure_minimal
  · intro z hz
    obtain ⟨hza, hzA, hzB⟩ := logCutoff_laplacian_ne_zero hAB hz
    have hr : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hza)
    exact ⟨((Real.lt_log_iff_exp_lt hr).mp hzA).le,
      ((Real.log_lt_iff_lt_exp hr).mp hzB).le⟩
  · exact isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)) |>.inter
      (isClosed_le (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const)

theorem integrable_mul_laplacian_logCutoff {f : ℂ → ℝ} (a : ℂ) {A B : ℝ}
    (hAB : A < B)
    (hf : ∀ z : ℂ, Real.exp A ≤ ‖z - a‖ → ‖z - a‖ ≤ Real.exp B → ContinuousAt f z) :
    Integrable (fun z : ℂ => f z * Δ (logCutoff a A B) z) := by
  have hc : Continuous (Δ (logCutoff a A B)) := continuous_iff_continuousAt.mpr
    (fun _ => laplacian_continuousAt ((logCutoff_contDiff a hAB).of_le (by norm_num)).contDiffAt)
  have hi := integrable_mul_of_local hc
    (laplacian_hasCompactSupport (logCutoff_hasCompactSupport a hAB)) (fun z hz => by
      obtain ⟨hzA, hzB⟩ := logCutoff_laplacian_tsupport hAB hz
      exact hf z hzA hzB)
  simpa only [mul_comm] using hi

theorem tendsto_integral_finite_end {f : ℂ → ℝ} (a : ℂ)
    (hf : Tendsto (fun z : ℂ =>
      (f z + Real.log ‖z - a‖) / (-Real.log ‖z - a‖)) (𝓝[≠] a) (𝓝 0))
    (hi : ∀ᶠ t : ℝ in atTop,
      Integrable (fun z : ℂ => f z * Δ (logCutoff a (-2*t) (-t)) z)) :
    Tendsto (fun t : ℝ => ∫ z : ℂ, f z * Δ (logCutoff a (-2*t) (-t)) z)
      atTop (𝓝 (-2 * Real.pi)) := by
  refine tendsto_integral_cutoff a (A := fun t => -2*t) (B := fun t => -t) ?_ ?_ ?_ hi ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    linarith
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [abs_of_neg (by linarith : -2*t < 0)]
    linarith
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [abs_of_neg (neg_neg_of_pos ht)]
    linarith
  · intro ε hε
    have he := hf.eventually (Metric.ball_mem_nhds 0 hε)
    obtain ⟨δ, hδ, hh⟩ := Metric.mem_nhdsWithin_iff.mp he
    filter_upwards [eventually_gt_atTop (-Real.log δ), eventually_gt_atTop (0 : ℝ)] with t ht htp
    intro z hza _ hzB
    have hr : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hza)
    have hzδ : ‖z - a‖ < δ := (Real.log_lt_log_iff hr hδ).mp (by linarith)
    have hh' := hh ⟨mem_ball_iff_norm.mpr hzδ, hza⟩
    have habs : |(f z + Real.log ‖z - a‖) / (-Real.log ‖z - a‖)| < ε := by
      simpa only [Set.mem_ofPred_eq, mem_ball, Real.dist_eq, sub_zero] using hh'
    have hzlog : Real.log ‖z - a‖ ≠ 0 := ne_of_lt (by linarith)
    rw [abs_div, abs_neg] at habs
    exact ((div_lt_iff₀ (abs_pos.mpr hzlog)).mp habs).le

theorem tendsto_integral_infinite_end {f : ℂ → ℝ} (a : ℂ)
    (hf : Tendsto (fun z : ℂ =>
      (f z + Real.log ‖z - a‖) / Real.log ‖z - a‖) (cocompact ℂ) (𝓝 0))
    (hi : ∀ᶠ t : ℝ in atTop,
      Integrable (fun z : ℂ => f z * Δ (logCutoff a t (2*t)) z)) :
    Tendsto (fun t : ℝ => ∫ z : ℂ, f z * Δ (logCutoff a t (2*t)) z)
      atTop (𝓝 (-2 * Real.pi)) := by
  refine tendsto_integral_cutoff a (A := fun t => t) (B := fun t => 2*t) ?_ ?_ ?_ hi ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    linarith
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [abs_of_pos ht]
    linarith
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [abs_of_pos (by linarith : 0 < 2*t)]
    linarith
  · intro ε hε
    have he := hf.eventually (Metric.ball_mem_nhds 0 hε)
    rw [← cobounded_eq_cocompact] at he
    obtain ⟨R, _, hh⟩ := (Metric.hasBasis_cobounded_compl_closedBall a).mem_iff.mp he
    filter_upwards [eventually_gt_atTop (Real.log (max R 1)),
      eventually_gt_atTop (0 : ℝ)] with t ht htp
    intro z hza hzA _
    have hr : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hza)
    have hR : 0 < max R 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hzR : R < ‖z - a‖ := (le_max_left R 1).trans_lt
      ((Real.log_lt_log_iff hR hr).mp (ht.trans hzA))
    have hh' := hh (by simpa only [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le] using hzR)
    have habs : |(f z + Real.log ‖z - a‖) / Real.log ‖z - a‖| < ε := by
      simpa only [Set.mem_ofPred_eq, mem_ball, Real.dist_eq, sub_zero] using hh'
    have hzlog : Real.log ‖z - a‖ ≠ 0 := ne_of_gt (htp.trans hzA)
    rw [abs_div] at habs
    exact ((div_lt_iff₀ (abs_pos.mpr hzlog)).mp habs).le

end AreaDeficit
