import ComplexApproximation.HalfStrip
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Convex

/-! # Uniform derivative bounds for the explicit half-strip map -/

open Set Complex Filter
open scoped Real Topology NNReal

namespace ComplexApproximation.HalfStrip

theorem deriv_map_mul_one_sub_exp {z : ℂ} (hz : z ∈ domain) :
    deriv map z * (1 - Complex.exp (-(2 * z))) = 1 + Complex.exp (-(2 * z)) := by
  rw [(hasDerivAt_map hz).deriv]
  have he : Complex.exp (-(2 * z)) = (Complex.exp z)⁻¹ * (Complex.exp z)⁻¹ := by
    rw [show -(2 * z) = -z + -z by ring, Complex.exp_add, Complex.exp_neg]
  have hid : Complex.cosh z * (1 - Complex.exp (-(2 * z))) =
      Complex.sinh z * (1 + Complex.exp (-(2 * z))) := by
    rw [he, Complex.sinh, Complex.cosh, Complex.exp_neg]
    field_simp
  rw [mul_assoc, hid, ← mul_assoc, inv_mul_cancel₀ (sinh_ne_zero hz), one_mul]

/-- The derivative is bounded above and bounded away from zero uniformly
on every part of the half-strip lying a positive distance to the right of
its finite endpoint. -/
theorem derivative_bounds {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : z ∈ domain)
    (hzη : η ≤ z.re) :
    (1 - Real.exp (-2 * η)) / (1 + Real.exp (-2 * η)) ≤ ‖deriv map z‖ ∧
    ‖deriv map z‖ ≤ (1 + Real.exp (-2 * η)) / (1 - Real.exp (-2 * η)) := by
  let q := Real.exp (-2 * η)
  let u := Complex.exp (-(2 * z))
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hu : ‖u‖ ≤ q := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    change -(2 * z.re - 0 * z.im) ≤ -2 * η
    linarith
  have hnumlo : 1 - q ≤ ‖1 + u‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (-u)
    simp only [norm_one, norm_neg, sub_neg_eq_add] at h
    linarith
  have hdenlo : 1 - q ≤ ‖1 - u‖ := by
    have h := norm_sub_norm_le (1 : ℂ) u
    simp only [norm_one] at h
    linarith
  have hnumhi : ‖1 + u‖ ≤ 1 + q :=
    (norm_add_le _ _).trans (by simpa using add_le_add_left hu 1)
  have hdenhi : ‖1 - u‖ ≤ 1 + q :=
    (norm_sub_le _ _).trans (by simpa using add_le_add_left hu 1)
  have hid : ‖deriv map z‖ * ‖1 - u‖ = ‖1 + u‖ := by
    simpa only [norm_mul] using congrArg norm (deriv_map_mul_one_sub_exp hz)
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < 1 + q)).mpr
    calc
      1 - q ≤ ‖1 + u‖ := hnumlo
      _ = ‖deriv map z‖ * ‖1 - u‖ := hid.symm
      _ ≤ ‖deriv map z‖ * (1 + q) := mul_le_mul_of_nonneg_left hdenhi (norm_nonneg _)
  · apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
    calc
      ‖deriv map z‖ * (1 - q) ≤ ‖deriv map z‖ * ‖1 - u‖ :=
        mul_le_mul_of_nonneg_left hdenlo (norm_nonneg _)
      _ = ‖1 + u‖ := hid
      _ ≤ 1 + q := hnumhi

theorem exists_uniform_derivative_bounds {η : ℝ} (hη : 0 < η) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z ∈ domain, η ≤ z.re →
      c ≤ ‖deriv map z‖ ∧ ‖deriv map z‖ ≤ C := by
  have hq : Real.exp (-2 * η) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  exact ⟨(1 - Real.exp (-2 * η)) / (1 + Real.exp (-2 * η)),
    (1 + Real.exp (-2 * η)) / (1 - Real.exp (-2 * η)),
    div_pos (sub_pos.mpr hq) (by positivity),
    div_pos (by positivity) (sub_pos.mpr hq), fun _ hz hzη => derivative_bounds hη hz hzη⟩

/-- A quantitative positive real part, useful for extending the map from
a closed half-strip to a bi-Lipschitz homeomorphism of the plane. -/
theorem re_derivative_lower_bound {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : z ∈ domain)
    (hzη : η ≤ z.re) :
    (1 - Real.exp (-2 * η)) / (1 + Real.exp (-2 * η)) ≤ (deriv map z).re := by
  let q := Real.exp (-2 * η)
  let u := Complex.exp (-(2 * z))
  let d := deriv map z
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hu : ‖u‖ ≤ q := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    change -(2 * z.re - 0 * z.im) ≤ -2 * η
    linarith
  have hid : d * (1 - u) = 1 + u := deriv_map_mul_one_sub_exp hz
  have hre := congrArg Complex.re hid
  have him := congrArg Complex.im hid
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im] at hre him
  have hn : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, pow_two]
  have hd : ‖1 - u‖ ^ 2 = (1 - u.re) ^ 2 + u.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    ring
  have heq : d.re * ‖1 - u‖ ^ 2 = 1 - ‖u‖ ^ 2 := by
    rw [hn, hd]
    linear_combination (1 - u.re) * hre - u.im * him
  have hpos : 0 < d.re := by
    have : 0 < 1 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
    nlinarith [sq_nonneg ‖1 - u‖]
  have hden : ‖1 - u‖ ≤ 1 + q :=
    (norm_sub_le _ _).trans (by simpa using add_le_add_left hu 1)
  apply (div_le_iff₀ (by positivity : 0 < 1 + q)).mpr
  have hsq : ‖u‖ ^ 2 ≤ q ^ 2 := by nlinarith [norm_nonneg u]
  have hdsq : ‖1 - u‖ ^ 2 ≤ (1 + q) ^ 2 := by nlinarith [norm_nonneg (1 - u)]
  have hmul := mul_le_mul_of_nonneg_left hdsq hpos.le
  nlinarith

def truncated (η : ℝ) : Set ℂ := domain ∩ {z | η ≤ z.re}

theorem convex_domain : Convex ℝ domain := by
  have he : domain = {z : ℂ | 0 < z.re} ∩
      ({z : ℂ | -(Real.pi / 2) < z.im} ∩ {z : ℂ | z.im < Real.pi / 2}) := by
    ext z
    simp [domain, abs_lt]
  rw [he]
  exact (convex_halfSpace_re_gt 0).inter
    ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _))

theorem convex_truncated (η : ℝ) : Convex ℝ (truncated η) :=
  convex_domain.inter (convex_halfSpace_re_ge η)

theorem exists_lipschitzOn_truncated {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ≥0, 0 < C ∧ LipschitzOnWith C map (truncated η) := by
  obtain ⟨c, C, hc, hC, hbounds⟩ := exists_uniform_derivative_bounds hη
  refine ⟨⟨C, hC.le⟩, hC, ?_⟩
  apply (convex_truncated η).lipschitzOnWith_of_nnnorm_deriv_le
    (fun z hz => (hasDerivAt_map hz.1).differentiableAt)
  intro z hz
  exact (hbounds z hz.1 hz.2).2

theorem tendsto_real_map_atTop :
    Tendsto (fun x : ℝ => Real.log (Real.sinh x)) atTop atTop :=
  Real.tendsto_log_atTop.comp Real.sinhOrderIso.tendsto_atTop

theorem tendsto_real_map_at_zero :
    Tendsto (fun x : ℝ => Real.log (Real.sinh x)) (𝓝[>] 0) atBot := by
  apply Real.tendsto_log_nhdsGT_zero.comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using (Real.continuous_sinh.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact Real.sinh_pos_iff.mpr hx

end ComplexApproximation.HalfStrip
