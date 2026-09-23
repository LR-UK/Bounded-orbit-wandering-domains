/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.TransitionMoments
import BoundedWanderingDomains.LogRadialIntegral
import Mathlib.MeasureTheory.Group.Integral

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace AreaDeficit

theorem transitionSecond_hasCompactSupport : HasCompactSupport transitionSecond :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) transitionSecond_tsupport

theorem integral_transitionSecond_univ : (∫ t : ℝ, transitionSecond t) = 0 := by
  rw [← integral_transitionSecond, intervalIntegral.integral_of_le zero_le_one]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  apply transitionSecond_eq_zero
  simp only [mem_Ioc, not_and_or, not_lt, not_le] at ht
  exact ht.imp id le_of_lt

theorem integral_mul_transitionSecond_univ : (∫ t : ℝ, t * transitionSecond t) = -1 := by
  rw [← integral_mul_transitionSecond, intervalIntegral.integral_of_le zero_le_one]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have hz : transitionSecond t = 0 := by
    apply transitionSecond_eq_zero
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at ht
    exact ht.imp id le_of_lt
  simp [hz]

theorem integrable_mul_transitionSecond : Integrable (fun t : ℝ => t * transitionSecond t) :=
  (continuous_id.mul transitionSecond_contDiff.continuous).integrable_of_hasCompactSupport
    transitionSecond_hasCompactSupport.mul_left

theorem integral_affine_rescale (f : ℝ → ℝ) (A : ℝ) {w : ℝ} (hw : 0 < w) :
    (∫ t : ℝ, f ((t - A) / w)) = w * ∫ s : ℝ, f s := by
  rw [integral_sub_right_eq_self (fun t : ℝ => f (t / w)) A,
    Measure.integral_comp_div, abs_of_pos hw, smul_eq_mul]

theorem integrable_affine_rescale {f : ℝ → ℝ} (hf : Integrable f)
    (A : ℝ) {w : ℝ} (hw : w ≠ 0) : Integrable (fun t : ℝ => f ((t - A) / w)) := by
  have h := ((integrable_comp_div_iff f hw).mpr hf).comp_add_right (-A)
  simpa only [sub_eq_add_neg] using h

/-- The one-dimensional kernel of the Laplacian of a logarithmic cutoff. -/
noncomputable def logKernel (A B : ℝ) (t : ℝ) : ℝ :=
  -transitionSecond ((t - A) / (B - A)) / (B - A) ^ 2

theorem logKernel_integrable {A B : ℝ} (hAB : A < B) : Integrable (logKernel A B) :=
  ((integrable_affine_rescale transitionSecond_integrable A
    (sub_pos.mpr hAB).ne').neg).div_const _

theorem integral_logKernel {A B : ℝ} (hAB : A < B) :
    (∫ t : ℝ, logKernel A B t) = 0 := by
  unfold logKernel
  rw [integral_div, integral_neg, integral_affine_rescale _ _ (sub_pos.mpr hAB),
    integral_transitionSecond_univ]
  simp

theorem integral_mul_logKernel {A B : ℝ} (hAB : A < B) :
    (∫ t : ℝ, t * logKernel A B t) = 1 := by
  let w := B - A
  have hw : 0 < w := sub_pos.mpr hAB
  let g : ℝ → ℝ := fun s => (A + w * s) * transitionSecond s
  have he : (fun t : ℝ => t * logKernel A B t) =
      (fun t : ℝ => -g ((t - A) / w) / w ^ 2) := by
    funext t
    dsimp [logKernel, g, w]
    field_simp [(sub_pos.mpr hAB).ne']
    ring
  have hg : (∫ s : ℝ, g s) = -w := by
    have he' : g = (fun s : ℝ => A * transitionSecond s + w * (s * transitionSecond s)) := by
      funext s
      dsimp [g]
      ring
    rw [he', integral_add (transitionSecond_integrable.const_mul A)
      (integrable_mul_transitionSecond.const_mul w), integral_const_mul, integral_const_mul,
      integral_transitionSecond_univ, integral_mul_transitionSecond_univ]
    ring
  rw [he, integral_div, integral_neg, integral_affine_rescale g A hw, hg]
  field_simp

theorem mul_logKernel_integrable {A B : ℝ} (hAB : A < B) :
    Integrable (fun t : ℝ => t * logKernel A B t) := by
  have hg : Integrable (fun s : ℝ => (A + (B - A) * s) * transitionSecond s) := by
    apply ((continuous_const.add (continuous_const.mul continuous_id)).mul
      transitionSecond_contDiff.continuous).integrable_of_hasCompactSupport
    exact transitionSecond_hasCompactSupport.mul_left
  have hi := ((integrable_affine_rescale hg A (sub_pos.mpr hAB).ne').neg).div_const
    ((B - A) ^ 2)
  apply hi.congr
  filter_upwards with t
  dsimp [logKernel]
  field_simp [(sub_pos.mpr hAB).ne']
  ring

/-- The logarithmic moment of every cutoff kernel is exactly `2π`. -/
theorem integral_log_radial_logKernel {A B : ℝ} (hAB : A < B) :
    (∫ z : ℂ, Real.log ‖z‖ * (logKernel A B (Real.log ‖z‖) / ‖z‖ ^ 2)) =
      2 * Real.pi := by
  have he : (fun z : ℂ => Real.log ‖z‖ * (logKernel A B (Real.log ‖z‖) / ‖z‖ ^ 2)) =
      (fun z : ℂ => (Real.log ‖z‖ * logKernel A B (Real.log ‖z‖)) / ‖z‖ ^ 2) := by
    funext z
    ring
  rw [he, integral_log_radial (fun t => t * logKernel A B t), integral_mul_logKernel hAB,
    mul_one]

end AreaDeficit
