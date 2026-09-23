/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.LogarithmicCutoff
import BoundedWanderingDomains.TransitionMoments
import BoundedWanderingDomains.ConformalLaplacian

open Metric Set Filter MeasureTheory InnerProductSpace Laplacian
open scoped Topology ContDiff

namespace AreaDeficit

theorem gradientSq_log_norm {z : ℂ} (hz : z ≠ 0) :
    gradientSq (fun w : ℂ => Real.log ‖w‖) z = 1 / ‖z‖ ^ 2 := by
  simp only [gradientSq, pd_log_norm hz]
  have h1 : inner ℝ z (1 : ℂ) = z.re := by
    simp [real_inner_eq_re_inner ℂ, RCLike.inner_apply]
  have hI : inner ℝ z Complex.I = z.im := by
    simp [real_inner_eq_re_inner ℂ, RCLike.inner_apply]
  rw [h1, hI, div_pow, div_pow, ← add_div]
  have hn : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hn]
  field_simp

theorem laplacian_logCutoff_zero {z : ℂ} (hz : z ≠ 0) (A B : ℝ) :
    Δ (logCutoff 0 A B) z =
      -transitionSecond ((Real.log ‖z‖ - A) / (B - A)) / ((B - A) ^ 2 * ‖z‖ ^ 2) := by
  let b : ℝ → ℝ := fun t => 1 - Real.smoothTransition ((t - A) / (B - A))
  let b₁ : ℝ → ℝ := fun t => -deriv Real.smoothTransition ((t - A) / (B - A)) / (B - A)
  let b₂ : ℝ → ℝ := fun t => -transitionSecond ((t - A) / (B - A)) / (B - A) ^ 2
  have hbc : ContDiff ℝ 2 b := by
    exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const _))
  have hb (t : ℝ) : HasDerivAt b (b₁ t) t := by
    have h := ((transition_hasDerivAt ((t - A) / (B - A))).comp t
      (((hasDerivAt_id t).sub_const A).div_const (B - A))).const_sub 1
    convert h using 1 <;> simp [b, b₁, div_eq_mul_inv]
  have hb₁ (t : ℝ) : HasDerivAt b₁ (b₂ t) t := by
    have h := (((transition_deriv_hasDerivAt ((t - A) / (B - A))).comp t
      (((hasDerivAt_id t).sub_const A).div_const (B - A))).neg).div_const (B - A)
    convert h using 1 <;> simp [b₁, b₂, div_eq_mul_inv, pow_two, mul_assoc]
  have hh : HarmonicAt (fun w : ℂ => Real.log ‖w‖) z :=
    analyticAt_id.harmonicAt_log_norm hz
  have he : logCutoff 0 A B =ᶠ[𝓝 z] (fun w : ℂ => b (Real.log ‖w‖)) := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    simp [logCutoff, hw, b]
  rw [(laplacian_congr_nhds he).eq_of_nhds,
    laplacian_comp hh.1 hbc hb hb₁, hh.2.eq_of_nhds, gradientSq_log_norm hz]
  simp only [Pi.zero_apply, mul_zero, zero_add, b₂]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem laplacian_logCutoff {a z : ℂ} (hz : z ≠ a) {A B : ℝ} (hAB : A < B) :
    Δ (logCutoff a A B) z =
      -transitionSecond ((Real.log ‖z - a‖ - A) / (B - A)) /
        ((B - A) ^ 2 * ‖z - a‖ ^ 2) := by
  have he : logCutoff a A B = logCutoff 0 A B ∘ (fun w : ℂ => w - a) := by
    funext w
    simp [logCutoff, sub_eq_zero]
  rw [he, laplacian_comp_holomorphic
    ((logCutoff_contDiff 0 hAB).of_le (by simp)).contDiffAt
    (by fun_prop : AnalyticAt ℂ (fun w : ℂ => w - a) z)]
  simp only [deriv_sub_const, deriv_id'', norm_one, one_pow, one_mul]
  exact laplacian_logCutoff_zero (sub_ne_zero.mpr hz) A B

end AreaDeficit
