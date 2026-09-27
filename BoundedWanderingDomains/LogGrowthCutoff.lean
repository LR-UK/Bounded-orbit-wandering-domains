/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.CutoffError

/-! # Logarithmic growth paired with a shrinking cutoff

This is the quantitative end estimate used in the surface point-insertion
argument.  A function with at most logarithmic growth has uniformly bounded
pairing with a cutoff whose transition width is comparable with its distance
down the logarithmic end.
-/

open Set Filter MeasureTheory InnerProductSpace Laplacian Metric
open scoped Topology ContDiff

namespace AreaDeficit

/-- Pairing a function of controlled logarithmic growth with the Laplacian of
a logarithmic cutoff.  The first term records the bounded part and decays as
the logarithmic transition widens; the second is uniform when the endpoints
are comparable with that width. -/
theorem integral_mul_laplacian_logCutoff_le_of_log_growth
    {f : ℂ → ℝ} (a : ℂ) {A B C L Q : ℝ}
    (hAB : A < B) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hA : |A| ≤ Q * (B - A)) (hB : |B| ≤ Q * (B - A))
    (hf : ∀ z : ℂ, z ≠ a → A < Real.log ‖z - a‖ →
      Real.log ‖z - a‖ < B →
      |f z| ≤ C + L * |Real.log ‖z - a‖|) :
    |∫ z : ℂ, f z * Δ (logCutoff a A B) z| ≤
      C * (2 * Real.pi * (∫ s : ℝ, |transitionSecond s|) / (B - A)) +
        L * (2 * Real.pi * Q * ∫ s : ℝ, |transitionSecond s|) := by
  let g : ℂ → ℝ := fun z =>
    C * |Δ (logCutoff a A B) z| +
      L * |Real.log ‖z - a‖ * Δ (logCutoff a A B) z|
  have hg : Integrable g :=
    ((integrable_abs_laplacian_logCutoff a hAB).const_mul C).add
      ((integrable_log_norm_laplacian_logCutoff a hAB).norm.const_mul L)
  have hpoint : ∀ z : ℂ,
      ‖f z * Δ (logCutoff a A B) z‖ ≤ g z := by
    intro z
    by_cases hz : Δ (logCutoff a A B) z = 0
    · simp [g, hz]
    · obtain ⟨hza, hzA, hzB⟩ := logCutoff_laplacian_ne_zero hAB hz
      have hm := mul_le_mul_of_nonneg_right (hf z hza hzA hzB)
        (abs_nonneg (Δ (logCutoff a A B) z))
      simpa only [Real.norm_eq_abs, abs_mul, add_mul, mul_assoc, g] using hm
  have hmain := norm_integral_le_of_norm_le hg (Eventually.of_forall hpoint)
  rw [Real.norm_eq_abs, integral_add,
    integral_const_mul, integral_const_mul,
    integral_abs_laplacian_logCutoff a hAB] at hmain
  · refine hmain.trans ?_
    gcongr
    exact integral_abs_log_norm_laplacian_logCutoff_le a hAB hA hB
  · exact (integrable_abs_laplacian_logCutoff a hAB).const_mul C
  · exact (integrable_log_norm_laplacian_logCutoff a hAB).norm.const_mul L

/-- Symmetric logarithmic annuli give a constant independent of their depth.
The bounded part tends to zero as `t` grows, while the logarithmic part has a
fixed bound. -/
theorem integral_mul_laplacian_logCutoff_neg_two_neg_one_le
    {f : ℂ → ℝ} (a : ℂ) {t C L : ℝ}
    (ht : 0 < t) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hf : ∀ z : ℂ, z ≠ a → -2 * t < Real.log ‖z - a‖ →
      Real.log ‖z - a‖ < -t →
      |f z| ≤ C + L * |Real.log ‖z - a‖|) :
    |∫ z : ℂ, f z * Δ (logCutoff a (-2 * t) (-t)) z| ≤
      C * (2 * Real.pi * (∫ s : ℝ, |transitionSecond s|) / t) +
        L * (2 * Real.pi * 2 * ∫ s : ℝ, |transitionSecond s|) := by
  have hAB : -2 * t < -t := by linarith
  have hA : |-2 * t| ≤ (2 : ℝ) * (-t - -2 * t) := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hB : |-t| ≤ (2 : ℝ) * (-t - -2 * t) := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have h := integral_mul_laplacian_logCutoff_le_of_log_growth
    (f := f) a hAB hC hL (Q := 2) hA hB hf
  convert h using 1 <;> ring

end AreaDeficit

#print axioms AreaDeficit.integral_mul_laplacian_logCutoff_le_of_log_growth
#print axioms AreaDeficit.integral_mul_laplacian_logCutoff_neg_two_neg_one_le
