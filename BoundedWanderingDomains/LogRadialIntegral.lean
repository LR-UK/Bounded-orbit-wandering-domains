/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

open Set MeasureTheory

namespace AreaDeficit

/-- Logarithmic polar coordinates for a radial kernel. -/
theorem integral_log_radial (f : ℝ → ℝ) :
    (∫ z : ℂ, f (Real.log ‖z‖) / ‖z‖ ^ 2) = 2 * Real.pi * ∫ t : ℝ, f t := by
  rw [integral_fun_norm_addHaar volume (fun r : ℝ => f (Real.log r) / r ^ 2)]
  simp only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul,
    Measure.real, Complex.volume_ball, ENNReal.ofReal_one, one_pow, one_mul,
    ENNReal.coe_toReal, NNReal.coe_real_pi]
  have he : (∫ r in Ioi (0 : ℝ), r * (f (Real.log r) / r ^ 2)) = ∫ t : ℝ, f t := by
    rw [← integral_comp_log_Ioi_zero f]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change r * (f (Real.log r) / r ^ 2) = r⁻¹ * f (Real.log r)
    field_simp
  rw [he]
  ring

theorem integrable_log_radial {f : ℝ → ℝ} (hf : Integrable f) :
    Integrable (fun z : ℂ => f (Real.log ‖z‖) / ‖z‖ ^ 2) := by
  rw [integrable_fun_norm_addHaar volume (f := fun r : ℝ => f (Real.log r) / r ^ 2)]
  simp only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul]
  apply ((integrableOn_comp_log_Ioi_zero f).mpr hf).congr_fun
    (fun r hr => ?_) measurableSet_Ioi
  change r⁻¹ * f (Real.log r) = r * (f (Real.log r) / r ^ 2)
  field_simp

end AreaDeficit
