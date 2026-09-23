import TauCeti.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

open Set Function

namespace FunctionTheory

set_option autoImplicit false

/-- A holomorphic function omitting both critical values of cosine admits a
holomorphic cosine lift on a simply connected open domain. This reuses the
attributed Tau Ceti logarithm and square-root branches. -/
theorem exists_analytic_cosine_lift {U : Set ℂ}
    (hU : IsOpen U) (hsc : IsSimplyConnected U) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U)
    (hplus : ∀ z∈U, f z≠1) (hminus : ∀ z∈U, f z≠-1) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ ∀ z∈U, Complex.cos (g z)=f z := by
  have hsqrt0 : (0:ℂ)∉(fun z => f z^2-1) '' U := by
    rintro ⟨z,hz,heq⟩
    exact (sq_ne_one_iff.mpr ⟨hplus z hz,hminus z hz⟩) (sub_eq_zero.mp heq)
  obtain ⟨q,hq,hq2⟩ := TauCeti.exists_differentiableOn_pow_eq hsc hU
    (hf.differentiableOn.pow 2 |>.sub_const 1) hsqrt0 (n:=2) (by norm_num)
  have hprod : ∀ z∈U, (f z+q z)*(f z-q z)=1 := by
    intro z hz
    calc
      (f z+q z)*(f z-q z) = f z^2-q z^2 := by ring
      _ = 1 := by
        have hqz : q z^2=f z^2-1 := hq2 hz
        rw [hqz]
        ring
  have hnonzero : ∀ z∈U, f z+q z≠0 := by
    intro z hz heq
    have H := hprod z hz
    rw [heq,zero_mul] at H
    exact zero_ne_one H
  obtain ⟨L,hL,hExp⟩ := TauCeti.exists_differentiableOn_eqOn_exp_comp hsc hU
    (hf.differentiableOn.add hq) (by rintro ⟨z,hz,heq⟩; exact hnonzero z hz heq)
  refine ⟨fun z => -Complex.I*L z,analyticOnNhd_const.mul (hL.analyticOnNhd hU),?_⟩
  intro z hz
  have hmul : (-Complex.I*L z)*Complex.I=L z := by
    calc
      (-Complex.I*L z)*Complex.I = -(Complex.I*Complex.I)*L z := by ring
      _ = L z := by rw [Complex.I_mul_I]; ring
  have he : Complex.exp (L z)=f z+q z := hExp hz
  have hinv : (f z+q z)⁻¹=f z-q z := by
    calc
      (f z+q z)⁻¹ = (f z+q z)⁻¹*((f z+q z)*(f z-q z)) := by rw [hprod z hz,mul_one]
      _ = f z-q z := by rw [← mul_assoc,inv_mul_cancel₀ (hnonzero z hz),one_mul]
  rw [Complex.cos,hmul,neg_mul,hmul,Complex.exp_neg,he,hinv]
  ring

end FunctionTheory
