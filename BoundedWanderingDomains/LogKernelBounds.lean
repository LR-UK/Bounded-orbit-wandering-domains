/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.LogKernelMoments
import BoundedWanderingDomains.CutoffLaplacian

open Set Filter MeasureTheory InnerProductSpace Laplacian Metric
open scoped Topology ContDiff

namespace AreaDeficit

theorem logKernel_eq_zero {A B t : ℝ} (hAB : A < B) (ht : t ≤ A ∨ B ≤ t) :
    logKernel A B t = 0 := by
  have hs : (t - A) / (B - A) ≤ 0 ∨ 1 ≤ (t - A) / (B - A) := by
    rcases ht with ht | ht
    · exact Or.inl (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_pos.mpr hAB).le)
    · exact Or.inr ((le_div_iff₀ (sub_pos.mpr hAB)).mpr (by linarith))
  simp [logKernel, transitionSecond_eq_zero hs]

theorem integral_abs_logKernel {A B : ℝ} (hAB : A < B) :
    (∫ t : ℝ, |logKernel A B t|) = (∫ s : ℝ, |transitionSecond s|) / (B - A) := by
  simp only [logKernel, abs_div, abs_neg, abs_pow, sq_abs]
  rw [integral_div, integral_affine_rescale (fun s : ℝ => |transitionSecond s|) A (sub_pos.mpr hAB)]
  field_simp [(sub_pos.mpr hAB).ne']

theorem integral_abs_mul_logKernel_le {A B L : ℝ} (hAB : A < B)
    (hA : |A| ≤ L * (B - A)) (hB : |B| ≤ L * (B - A)) :
    (∫ t : ℝ, |t * logKernel A B t|) ≤ L * ∫ s : ℝ, |transitionSecond s| := by
  have hnorm : ∀ t : ℝ, |t * logKernel A B t| ≤ L * (B - A) * |logKernel A B t| := by
    intro t
    by_cases hz : logKernel A B t = 0
    · simp [hz]
    have hAt : A < t := lt_of_not_ge (fun h => hz (logKernel_eq_zero hAB (Or.inl h)))
    have htB : t < B := lt_of_not_ge (fun h => hz (logKernel_eq_zero hAB (Or.inr h)))
    have ht : |t| ≤ L * (B - A) := by
      apply abs_le.mpr
      constructor
      · have := neg_abs_le A
        linarith
      · exact htB.le.trans ((le_abs_self B).trans hB)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)
  have hi : Integrable (fun t : ℝ => |t * logKernel A B t|) := by
    simpa only [Real.norm_eq_abs] using (mul_logKernel_integrable hAB).norm
  have hj : Integrable (fun t : ℝ => L * (B - A) * |logKernel A B t|) := by
    simpa only [Real.norm_eq_abs] using (logKernel_integrable hAB).norm.const_mul (L * (B - A))
  have h := integral_mono hi hj hnorm
  rw [integral_const_mul, integral_abs_logKernel hAB] at h
  convert h using 1
  field_simp [(sub_pos.mpr hAB).ne']

theorem laplacian_logCutoff_eq_kernel (a z : ℂ) {A B : ℝ} (hAB : A < B) :
    Δ (logCutoff a A B) z = logKernel A B (Real.log ‖z - a‖) / ‖z - a‖ ^ 2 := by
  by_cases hz : z = a
  · subst z
    have he : logCutoff a A B =ᶠ[𝓝 a] (fun _ => 1) := by
      filter_upwards [Metric.ball_mem_nhds a (Real.exp_pos A)] with w hw
      exact logCutoff_eq_one hAB (by simpa [dist_eq_norm] using (mem_ball.mp hw).le)
    rw [(laplacian_congr_nhds he).eq_of_nhds]
    simp
  · rw [laplacian_logCutoff hz hAB]
    dsimp [logKernel]
    rw [div_div]

theorem integrable_log_norm_laplacian_logCutoff (a : ℂ) {A B : ℝ} (hAB : A < B) :
    Integrable (fun z : ℂ => Real.log ‖z - a‖ * Δ (logCutoff a A B) z) := by
  have h := (integrable_log_radial (mul_logKernel_integrable hAB)).comp_add_right (-a)
  apply h.congr
  filter_upwards with z
  rw [laplacian_logCutoff_eq_kernel a z hAB]
  simp only [sub_eq_add_neg]
  ring

theorem integral_log_norm_laplacian_logCutoff (a : ℂ) {A B : ℝ} (hAB : A < B) :
    (∫ z : ℂ, Real.log ‖z - a‖ * Δ (logCutoff a A B) z) = 2 * Real.pi := by
  simp_rw [laplacian_logCutoff_eq_kernel a _ hAB]
  rw [integral_sub_right_eq_self
    (fun z : ℂ => Real.log ‖z‖ * (logKernel A B (Real.log ‖z‖) / ‖z‖ ^ 2)) a]
  exact integral_log_radial_logKernel hAB

theorem integral_abs_log_norm_laplacian_logCutoff_le (a : ℂ) {A B L : ℝ} (hAB : A < B)
    (hA : |A| ≤ L * (B - A)) (hB : |B| ≤ L * (B - A)) :
    (∫ z : ℂ, |Real.log ‖z - a‖ * Δ (logCutoff a A B) z|) ≤
      2 * Real.pi * L * ∫ s : ℝ, |transitionSecond s| := by
  simp_rw [laplacian_logCutoff_eq_kernel a _ hAB]
  rw [integral_sub_right_eq_self
    (fun z : ℂ => |Real.log ‖z‖ * (logKernel A B (Real.log ‖z‖) / ‖z‖ ^ 2)|) a]
  have he : (fun z : ℂ => |Real.log ‖z‖ * (logKernel A B (Real.log ‖z‖) / ‖z‖ ^ 2)|) =
      (fun z : ℂ => |Real.log ‖z‖ * logKernel A B (Real.log ‖z‖)| / ‖z‖ ^ 2) := by
    funext z
    rw [← mul_div_assoc, abs_div, abs_of_nonneg (sq_nonneg ‖z‖)]
  rw [he, integral_log_radial (fun t => |t * logKernel A B t|)]
  have h := mul_le_mul_of_nonneg_left (integral_abs_mul_logKernel_le hAB hA hB)
    (show 0 ≤ 2 * Real.pi by positivity)
  simpa only [mul_assoc] using h

end AreaDeficit
