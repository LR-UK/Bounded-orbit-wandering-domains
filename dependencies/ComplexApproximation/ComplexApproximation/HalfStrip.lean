import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-! # An explicit conformal map on a half-strip

The map `log (sinh z)` sends the right half of the strip `|im z| < π/2`
into that strip. It sends the positive real axis onto the real axis. This
provides the elementary conformal map needed for the straight half-strips
in the singleton counterexample, without Schwarz reflection.
-/

open Set Complex
open scoped Real Topology

namespace ComplexApproximation.HalfStrip

def domain : Set ℂ := {z | 0 < z.re ∧ |z.im| < Real.pi / 2}

noncomputable def map (z : ℂ) : ℂ := Complex.log (Complex.sinh z)

theorem isOpen_domain : IsOpen domain :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_im.abs continuous_const)

theorem sinh_re (z : ℂ) : (Complex.sinh z).re = Real.sinh z.re * Real.cos z.im := by
  rw [Complex.sinh, Complex.div_ofNat_re, Complex.sub_re, Complex.exp_re,
    Complex.exp_re, Complex.neg_re, Complex.neg_im, Real.cos_neg, Real.sinh_eq]
  ring

theorem cosh_re (z : ℂ) : (Complex.cosh z).re = Real.cosh z.re * Real.cos z.im := by
  rw [Complex.cosh, Complex.div_ofNat_re, Complex.add_re, Complex.exp_re,
    Complex.exp_re, Complex.neg_re, Complex.neg_im, Real.cos_neg, Real.cosh_eq]
  ring

theorem sinh_re_pos {z : ℂ} (hz : z ∈ domain) : 0 < (Complex.sinh z).re := by
  rw [sinh_re]
  exact mul_pos (Real.sinh_pos_iff.mpr hz.1) (Real.cos_pos_of_mem_Ioo (abs_lt.mp hz.2))

theorem cosh_re_pos {z : ℂ} (hz : z ∈ domain) : 0 < (Complex.cosh z).re := by
  rw [cosh_re]
  exact mul_pos (Real.cosh_pos _) (Real.cos_pos_of_mem_Ioo (abs_lt.mp hz.2))

theorem sinh_ne_zero {z : ℂ} (hz : z ∈ domain) : Complex.sinh z ≠ 0 := by
  intro h
  have := sinh_re_pos hz
  simp [h] at this

theorem cosh_ne_zero {z : ℂ} (hz : z ∈ domain) : Complex.cosh z ≠ 0 := by
  intro h
  have := cosh_re_pos hz
  simp [h] at this

theorem hasDerivAt_map {z : ℂ} (hz : z ∈ domain) :
    HasDerivAt map ((Complex.sinh z)⁻¹ * Complex.cosh z) z :=
  (Complex.hasDerivAt_log (Or.inl (sinh_re_pos hz))).comp z (Complex.hasDerivAt_sinh z)

theorem differentiableOn_map : DifferentiableOn ℂ map domain :=
  fun _ hz => (hasDerivAt_map hz).differentiableAt.differentiableWithinAt

theorem deriv_map_ne_zero {z : ℂ} (hz : z ∈ domain) : deriv map z ≠ 0 := by
  rw [(hasDerivAt_map hz).deriv]
  exact mul_ne_zero (inv_ne_zero (sinh_ne_zero hz)) (cosh_ne_zero hz)

theorem abs_im_map_lt {z : ℂ} (hz : z ∈ domain) : |(map z).im| < Real.pi / 2 := by
  rw [map, Complex.log_im, Complex.abs_arg_lt_pi_div_two_iff]
  exact Or.inl (sinh_re_pos hz)

theorem injOn_sinh : InjOn Complex.sinh domain := by
  intro z hz w hw hzw
  have hfactor : (Complex.exp z - Complex.exp w) *
      (Complex.exp z * Complex.exp w + 1) = 0 := by
    have h := congrArg (fun a : ℂ => 2 * a) hzw
    simp only [Complex.two_sinh, Complex.exp_neg] at h
    field_simp at h
    linear_combination h
  rcases mul_eq_zero.mp hfactor with h | h
  · apply Complex.exp_inj_of_neg_pi_lt_of_le_pi
      (by linarith [(abs_lt.mp hz.2).1, Real.pi_pos])
      (by linarith [(abs_lt.mp hz.2).2, Real.pi_pos])
      (by linarith [(abs_lt.mp hw.2).1, Real.pi_pos])
      (by linarith [(abs_lt.mp hw.2).2, Real.pi_pos])
    exact sub_eq_zero.mp h
  · have he : Complex.exp (z + w) = -1 := by rw [Complex.exp_add]; linear_combination h
    have hn := congrArg norm he
    simp only [Complex.norm_exp, Complex.add_re, norm_neg, norm_one] at hn
    have hr : 0 < z.re + w.re := add_pos hz.1 hw.1
    have ht := Real.one_lt_exp_iff.mpr hr
    linarith

theorem injOn_map : InjOn map domain := by
  intro z hz w hw h
  apply injOn_sinh hz hw
  have he := congrArg Complex.exp h
  simpa only [map, Complex.exp_log (sinh_ne_zero hz), Complex.exp_log (sinh_ne_zero hw)] using he

theorem map_ofReal {x : ℝ} (hx : 0 < x) : map x = (Real.log (Real.sinh x) : ℂ) := by
  rw [map, ← Complex.ofReal_sinh, ← Complex.ofReal_log (Real.sinh_pos_iff.mpr hx).le]

theorem real_axis_surjective (y : ℝ) : ∃ x : ℝ, 0 < x ∧ map x = (y : ℂ) := by
  refine ⟨Real.arsinh (Real.exp y), Real.arsinh_pos_iff.mpr (Real.exp_pos y), ?_⟩
  rw [map_ofReal (Real.arsinh_pos_iff.mpr (Real.exp_pos y)), Real.sinh_arsinh, Real.log_exp]

end ComplexApproximation.HalfStrip
