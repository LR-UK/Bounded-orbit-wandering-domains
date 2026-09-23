import Runge.CauchyGreen
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Complex.Conformal

/-!
# The planar Cauchy transform

The singular kernel is locally integrable in two real dimensions. Convolution
with a smooth compactly supported density is therefore smooth, including at
points in the support of the density.
-/

open Complex MeasureTheory Set Function
open scoped Topology ContDiff Convolution

namespace ComplexApproximation

/-- The Cauchy kernel, with the harmless totalised value zero at the origin. -/
noncomputable def cauchyKernel (z : ℂ) : ℂ := z⁻¹

theorem locallyIntegrable_cauchyKernel : LocallyIntegrable cauchyKernel := by
  apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1)
    (by simp [Complex.finrank_real_complex]) (by norm_num [Complex.finrank_real_complex])
  · exact Filter.Eventually.of_forall (fun z => by
      simp [cauchyKernel, norm_inv, Real.rpow_neg_one])
  · exact measurable_inv.aestronglyMeasurable

/-- The unnormalised planar Cauchy transform. The integration variable is the
kernel variable; this form makes differentiation fall on the smooth density. -/
noncomputable def cauchyTransform (q : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ w : ℂ, w⁻¹ * q (z - w)

theorem cauchyTransform_eq_convolution (q : ℂ → ℂ) :
    cauchyTransform q = cauchyKernel ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] q := rfl

theorem contDiff_cauchyTransform {q : ℂ → ℂ} {n : ℕ∞}
    (hq : ContDiff ℝ n q) (hc : HasCompactSupport q) :
    ContDiff ℝ n (cauchyTransform q) := by
  rw [cauchyTransform_eq_convolution]
  exact hc.contDiff_convolution_right _ locallyIntegrable_cauchyKernel hq

theorem integrable_cauchyTransform_integrand {q : ℂ → ℂ}
    (hq : Continuous q) (hc : HasCompactSupport q) (z : ℂ) :
    Integrable (fun w : ℂ => w⁻¹ * q (z - w)) := by
  exact hc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ)
    locallyIntegrable_cauchyKernel hq z

theorem cauchyTransform_eq_integral (q : ℂ → ℂ) (z : ℂ) :
    cauchyTransform q z = ∫ w : ℂ, q w / (z - w) := by
  have h := integral_sub_left_eq_self (fun w : ℂ => q w / (z - w)) volume z
  simpa [cauchyTransform, div_eq_mul_inv, mul_comm] using h

theorem integrable_div_sub {q : ℂ → ℂ}
    (hq : Continuous q) (hc : HasCompactSupport q) (z : ℂ) :
    Integrable (fun w : ℂ => q w / (z - w)) := by
  have h := hc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℂ)
    hq locallyIntegrable_cauchyKernel z
  change Integrable (fun w : ℂ => q w * (z - w)⁻¹) at h
  simpa only [div_eq_mul_inv] using h

theorem fderiv_cauchyTransform_apply {q : ℂ → ℂ}
    (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q) (z v : ℂ) :
    fderiv ℝ (cauchyTransform q) z v =
      cauchyTransform (fun w => fderiv ℝ q w v) z := by
  rw [cauchyTransform_eq_convolution,
    (hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
      locallyIntegrable_cauchyKernel (hq.of_le (by simp)) z).fderiv]
  exact convolution_precompR_apply _ locallyIntegrable_cauchyKernel
    (hc.fderiv ℝ) (hq.continuous_fderiv (by simp)) z v

/-- Real differentiation can be passed to the compactly supported density. -/
theorem cauchyRiemannDefect_cauchyTransform {q : ℂ → ℂ}
    (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q) (z : ℂ) :
    Runge.cauchyRiemannDefect (cauchyTransform q) z =
      cauchyTransform (Runge.cauchyRiemannDefect q) z := by
  have hcont (v : ℂ) : Continuous (fun w => fderiv ℝ q w v) :=
    (hq.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)
  have hi (v : ℂ) := integrable_cauchyTransform_integrand (hcont v)
    (hc.fderiv_apply ℝ v) z
  simp only [Runge.cauchyRiemannDefect, fderiv_cauchyTransform_apply hq hc,
    cauchyTransform]
  rw [← integral_const_mul, ← integral_sub ((hi 1).const_mul I) (hi I)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w => by ring)

theorem differentiableAt_complex_iff_defect_eq_zero {q : ℂ → ℂ} {z : ℂ}
    (hq : DifferentiableAt ℝ q z) :
    DifferentiableAt ℂ q z ↔ Runge.cauchyRiemannDefect q z = 0 := by
  rw [differentiableAt_complex_iff_differentiableAt_real]
  simp only [hq, true_and, Runge.cauchyRiemannDefect, sub_eq_zero, smul_eq_mul]
  exact eq_comm

end ComplexApproximation
