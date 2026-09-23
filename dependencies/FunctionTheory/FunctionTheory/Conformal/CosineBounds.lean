import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

namespace FunctionTheory

set_option autoImplicit false

/-- The norm identity controlling the imaginary part of a cosine lift. -/
theorem norm_cos_sq (z : ℂ) :
    ‖Complex.cos z‖^2=Real.cos z.re^2+Real.sinh z.im^2 := by
  have heq : Complex.cos z=(Real.cos z.re*Real.cosh z.im:ℝ)-
      (Real.sin z.re*Real.sinh z.im:ℝ)*Complex.I := by
    simpa using Complex.cos_eq z
  rw [heq,← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    mul_zero,mul_one,sub_zero,zero_sub,add_zero]
  calc
    _ = Real.cos z.re^2*Real.cosh z.im^2+Real.sin z.re^2*Real.sinh z.im^2 := by ring
    _ =
        Real.cos z.re^2*(Real.cosh z.im^2-Real.sinh z.im^2)+
        (Real.sin z.re^2+Real.cos z.re^2)*Real.sinh z.im^2 := by ring
    _ = Real.cos z.re^2+Real.sinh z.im^2 := by
      rw [Real.cosh_sq_sub_sinh_sq,Real.sin_sq_add_cos_sq]
      ring

/-- The imaginary part of any cosine preimage is bounded by the norm of
its image. Real translations by periods can therefore bound the whole lift. -/
theorem abs_im_le_norm_cos (z : ℂ) : |z.im|≤‖Complex.cos z‖ := by
  have hsq := norm_cos_sq z
  have hsn : |Real.sinh z.im|≤‖Complex.cos z‖ := by
    nlinarith [sq_nonneg (Real.cos z.re),sq_abs (Real.sinh z.im),
      abs_nonneg (Real.sinh z.im),norm_nonneg (Complex.cos z)]
  have him : |z.im|≤|Real.sinh z.im| := by
    by_cases h : 0≤z.im
    · rw [abs_of_nonneg h,abs_of_nonneg (Real.sinh_nonneg_iff.mpr h)]
      exact Real.self_le_sinh_iff.mpr h
    · have h' : z.im≤0 := le_of_not_ge h
      rw [abs_of_nonpos h',abs_of_nonpos (Real.sinh_nonpos_iff.mpr h')]
      exact neg_le_neg (Real.sinh_le_self_iff.mpr h')
  exact him.trans hsn

end FunctionTheory
