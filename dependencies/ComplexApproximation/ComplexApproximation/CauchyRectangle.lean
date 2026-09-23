import Runge.RectangleKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The Cauchy kernel integral around a square -/

open Complex MeasureTheory Set Runge
open scoped Topology

namespace ComplexApproximation

theorem rectangleBoundary_inv (R : ℝ) (hR : 0 < R) :
    rectangleBoundary (fun w : ℂ => w⁻¹) ⟨-R, -R⟩ ⟨R, R⟩ = 2 * Real.pi * I := by
  have cb : Continuous (fun x : ℝ => ((x : ℂ) + ↑(-R) * I)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro x
    apply complex_ne_zero_of_im_neg
    simpa using (neg_neg_of_pos hR)
  have ct : Continuous (fun x : ℝ => ((x : ℂ) + R * I)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro x
    apply complex_ne_zero_of_im_pos
    simpa using hR
  have cr : Continuous (fun y : ℝ => ((R : ℂ) + y * I)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro x
    apply complex_ne_zero_of_re_pos
    simpa using hR
  have cl : Continuous (fun y : ℝ => ((↑(-R) : ℂ) + y * I)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro x
    apply complex_ne_zero_of_re_neg
    simpa using (neg_neg_of_pos hR)
  have hp (x : ℝ) :
      ((x : ℂ) + ↑(-R) * I)⁻¹ - ((x : ℂ) + R * I)⁻¹ +
          I * ((R : ℂ) + x * I)⁻¹ - I * ((↑(-R) : ℂ) + x * I)⁻¹ =
        (4 * I * R) * ((R ^ 2 + x ^ 2)⁻¹ : ℝ) := by
    apply Complex.ext <;>
      simp [Complex.inv_re, Complex.inv_im, Complex.normSq_apply, pow_two, add_comm] <;> ring
  rw [rectangleBoundary]
  simp only
  have hbt : IntervalIntegrable
      (fun x : ℝ => ((x : ℂ) + ↑(-R) * I)⁻¹ - ((x : ℂ) + R * I)⁻¹)
      volume (-R) R := (cb.sub ct).intervalIntegrable _ _
  have hir : IntervalIntegrable (fun x : ℝ => I * ((R : ℂ) + x * I)⁻¹)
      volume (-R) R := (continuous_const.mul cr).intervalIntegrable _ _
  have hil : IntervalIntegrable (fun x : ℝ => I * ((↑(-R) : ℂ) + x * I)⁻¹)
      volume (-R) R := (continuous_const.mul cl).intervalIntegrable _ _
  have hbtr : IntervalIntegrable
      (fun x : ℝ => ((x : ℂ) + ↑(-R) * I)⁻¹ - ((x : ℂ) + R * I)⁻¹ +
        I * ((R : ℂ) + x * I)⁻¹) volume (-R) R := hbt.add hir
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (cb.intervalIntegrable _ _) (ct.intervalIntegrable _ _),
    ← intervalIntegral.integral_add hbt hir,
    ← intervalIntegral.integral_sub hbtr hil]
  simp_rw [hp]
  rw [intervalIntegral.integral_const_mul]
  have hc : Continuous (fun x : ℝ => (R ^ 2 + x ^ 2)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro x
    positivity
  have he := Complex.ofRealCLM.intervalIntegral_comp_comm
    (hc.intervalIntegrable (μ := volume) (-R) R)
  simp only [Complex.ofRealCLM_apply] at he
  rw [he]
  simp only [integral_inv_sq_add_sq hR.ne',
    div_self hR.ne', neg_div, Real.arctan_neg, Real.arctan_one,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_inv, Complex.ofReal_ofNat]
  have hcR : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  field_simp
  ring

end ComplexApproximation
