import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The model ideal-triangle integral, curvature −1

The standard ideal triangle with vertices −1, 1, ∞ in the upper half-plane
has vertical sections y > √(1 − x²), for −1 < x < 1. These lemmas evaluate
the corresponding iterated integral of y⁻² directly, without Gauss–Bonnet.
They do not assert existence of an ideal triangulation of a punctured sphere.
-/

open Set MeasureTheory Real

namespace AreaDeficit

theorem integral_inverse_sqrt_semicircle :
    (∫ x in (-1 : ℝ)..1, 1 / Real.sqrt (1 - x^2)) = Real.pi := by
  have hd : ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x^2)) x :=
    fun x hx => Real.hasDerivAt_arcsin (ne_of_gt hx.1) (ne_of_lt hx.2)
  have hi : IntervalIntegrable (fun x : ℝ => 1 / Real.sqrt (1 - x^2)) volume (-1) 1 := by
    apply intervalIntegral.intervalIntegrable_deriv_of_nonneg Real.continuous_arcsin.continuousOn
    · simpa using hd
    · intro x hx
      positivity
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (-1 : ℝ) ≤ 1)
    Real.continuous_arcsin.continuousOn hd hi
  simpa using he

theorem integral_upper_halfPlane_vertical {c : ℝ} (hc : 0 < c) :
    (∫ y in Ioi c, (y^2)⁻¹) = c⁻¹ := by
  have he := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hc
  have hr (y : ℝ) : y ^ (-2 : ℝ) = (y^2)⁻¹ := by
    simp
  simpa only [show (-2 : ℝ) + 1 = -1 by norm_num, hr,
    Real.rpow_neg_one, div_neg, div_one, neg_neg] using he

theorem idealTriangle_iterated_integral :
    (∫ x in (-1 : ℝ)..1, ∫ y in Ioi (Real.sqrt (1 - x^2)), (y^2)⁻¹) = Real.pi := by
  rw [← integral_inverse_sqrt_semicircle]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  have hs : 0 < 1 - x^2 := by
    nlinarith [mul_pos (sub_pos.mpr hx.2) (by linarith [hx.1] : 0 < 1 + x)]
  simpa only [one_div] using integral_upper_halfPlane_vertical (Real.sqrt_pos.mpr hs)

end AreaDeficit
