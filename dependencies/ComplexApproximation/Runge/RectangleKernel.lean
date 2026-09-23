import Runge.CauchyGreen

open Complex MeasureTheory Set

namespace Runge

theorem complex_ne_zero_of_im_neg {w : ℂ} (hw : w.im < 0) : w ≠ 0 := by
  intro h
  simp [h] at hw

theorem complex_ne_zero_of_im_pos {w : ℂ} (hw : 0 < w.im) : w ≠ 0 := by
  intro h
  simp [h] at hw

theorem complex_ne_zero_of_re_pos {w : ℂ} (hw : 0 < w.re) : w ≠ 0 := by
  intro h
  simp [h] at hw

theorem complex_ne_zero_of_re_neg {w : ℂ} (hw : w.re < 0) : w ≠ 0 := by
  intro h
  simp [h] at hw

theorem inv_im_pos_of_im_neg {w : ℂ} (hw : w.im < 0) : 0 < w⁻¹.im := by
  rw [Complex.inv_im]
  exact div_pos (neg_pos.mpr hw) (normSq_pos.mpr (complex_ne_zero_of_im_neg hw))

theorem neg_inv_im_pos_of_im_pos {w : ℂ} (hw : 0 < w.im) : 0 < -w⁻¹.im := by
  rw [Complex.inv_im, neg_div, neg_neg]
  exact div_pos hw (normSq_pos.mpr (complex_ne_zero_of_im_pos hw))

theorem inv_re_pos_of_re_pos {w : ℂ} (hw : 0 < w.re) : 0 < w⁻¹.re := by
  rw [Complex.inv_re]
  exact div_pos hw (normSq_pos.mpr (complex_ne_zero_of_re_pos hw))

theorem neg_inv_re_pos_of_re_neg {w : ℂ} (hw : w.re < 0) : 0 < -w⁻¹.re := by
  rw [Complex.inv_re, ← neg_div]
  exact div_pos (neg_pos.mpr hw) (normSq_pos.mpr (complex_ne_zero_of_re_neg hw))

theorem rectangleKernel_im_pos (a b z : ℂ)
    (hax : a.re < z.re) (hxb : z.re < b.re)
    (hay : a.im < z.im) (hyb : z.im < b.im) :
    0 < (rectangleBoundary (fun w => (w-z)⁻¹) a b).im := by
  have hbot (t : ℝ) : (t + a.im * I - z).im < 0 := by simp; linarith
  have htop (t : ℝ) : 0 < (t + b.im * I - z).im := by simp; linarith
  have hright (t : ℝ) : 0 < (b.re + t * I - z).re := by simp; linarith
  have hleft (t : ℝ) : (a.re + t * I - z).re < 0 := by simp; linarith
  have cb : Continuous (fun t : ℝ => (t + a.im * I - z)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    exact fun t => complex_ne_zero_of_im_neg (hbot t)
  have ct : Continuous (fun t : ℝ => (t + b.im * I - z)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    exact fun t => complex_ne_zero_of_im_pos (htop t)
  have cr : Continuous (fun t : ℝ => (b.re + t * I - z)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    exact fun t => complex_ne_zero_of_re_pos (hright t)
  have cl : Continuous (fun t : ℝ => (a.re + t * I - z)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    exact fun t => complex_ne_zero_of_re_neg (hleft t)
  have pb : 0 < ∫ t in a.re..b.re, ((t : ℂ) + a.im * I - z)⁻¹.im := by
    apply intervalIntegral.integral_pos (hax.trans hxb) (Complex.continuous_im.comp cb).continuousOn
    · exact fun t _ => (inv_im_pos_of_im_neg (hbot t)).le
    · exact ⟨a.re, ⟨le_rfl, (hax.trans hxb).le⟩, inv_im_pos_of_im_neg (hbot _)⟩
  have pt : 0 < ∫ t in a.re..b.re, -((t : ℂ) + b.im * I - z)⁻¹.im := by
    apply intervalIntegral.integral_pos (hax.trans hxb) (Complex.continuous_im.comp ct).neg.continuousOn
    · exact fun t _ => (neg_inv_im_pos_of_im_pos (htop t)).le
    · exact ⟨a.re, ⟨le_rfl, (hax.trans hxb).le⟩, neg_inv_im_pos_of_im_pos (htop _)⟩
  have pr : 0 < ∫ t in a.im..b.im, ((b.re : ℂ) + t * I - z)⁻¹.re := by
    apply intervalIntegral.integral_pos (hay.trans hyb) (Complex.continuous_re.comp cr).continuousOn
    · exact fun t _ => (inv_re_pos_of_re_pos (hright t)).le
    · exact ⟨a.im, ⟨le_rfl, (hay.trans hyb).le⟩, inv_re_pos_of_re_pos (hright _)⟩
  have pl : 0 < ∫ t in a.im..b.im, -((a.re : ℂ) + t * I - z)⁻¹.re := by
    apply intervalIntegral.integral_pos (hay.trans hyb) (Complex.continuous_re.comp cl).neg.continuousOn
    · exact fun t _ => (neg_inv_re_pos_of_re_neg (hleft t)).le
    · exact ⟨a.im, ⟨le_rfl, (hay.trans hyb).le⟩, neg_inv_re_pos_of_re_neg (hleft _)⟩
  simp only [intervalIntegral.integral_neg] at pt pl
  have eb := (Complex.imCLM.intervalIntegral_comp_comm (cb.intervalIntegrable (μ := volume) a.re b.re)).symm
  have et := (Complex.imCLM.intervalIntegral_comp_comm (ct.intervalIntegrable (μ := volume) a.re b.re)).symm
  have er := (Complex.reCLM.intervalIntegral_comp_comm (cr.intervalIntegrable (μ := volume) a.im b.im)).symm
  have el := (Complex.reCLM.intervalIntegral_comp_comm (cl.intervalIntegrable (μ := volume) a.im b.im)).symm
  simp only [Complex.imCLM_apply, Complex.reCLM_apply] at eb et er el
  simp only [rectangleBoundary, sub_im, add_im, mul_im, I_re, I_im,
    zero_mul, one_mul, zero_add]
  rw [eb, et, er, el]
  linarith

theorem rectangleKernel_ne_zero (a b z : ℂ)
    (hax : a.re < z.re) (hxb : z.re < b.re)
    (hay : a.im < z.im) (hyb : z.im < b.im) :
    rectangleBoundary (fun w => (w-z)⁻¹) a b ≠ 0 :=
  complex_ne_zero_of_im_pos (rectangleKernel_im_pos a b z hax hxb hay hyb)

end Runge
