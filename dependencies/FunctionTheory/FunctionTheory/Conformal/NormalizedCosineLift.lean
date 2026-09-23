import FunctionTheory.Conformal.CosineLift
import FunctionTheory.Conformal.CosineBounds
import Mathlib.Algebra.Order.ToIntervalMod

open Set Function

namespace FunctionTheory

set_option autoImplicit false

/-- A period translate of a cosine preimage has controlled norm. -/
theorem exists_cosine_period_translate_norm_le (z : ℂ) :
    ∃ n : ℤ, ‖z+(n:ℂ)*(2*Real.pi)‖≤Real.pi+‖Complex.cos z‖ := by
  obtain ⟨n,hn,hu⟩ := existsUnique_add_zsmul_mem_Ioc Real.two_pi_pos z.re (-Real.pi)
  let w := z+(n:ℂ)*(2*Real.pi)
  have hre : |w.re|≤Real.pi := by
    rw [abs_le]
    have H : -Real.pi<z.re+(n:ℝ)*(2*Real.pi) ∧
        z.re+(n:ℝ)*(2*Real.pi)≤-Real.pi+2*Real.pi := by
      simpa only [mem_Ioc,zsmul_eq_mul] using hn
    have hw : w.re=z.re+(n:ℝ)*(2*Real.pi) := by simp [w]
    rw [hw]
    constructor <;> linarith
  have him : w.im=z.im := by simp [w]
  refine ⟨n,?_⟩
  change ‖w‖≤_
  calc
    ‖w‖ ≤ |w.re|+|w.im| := Complex.norm_le_abs_re_add_abs_im w
    _ ≤ Real.pi+‖Complex.cos z‖ := by rw [him]; exact add_le_add hre (abs_im_le_norm_cos z)

/-- A holomorphic cosine lift can be normalized at a prescribed point
without changing the image function. -/
theorem exists_normalized_analytic_cosine_lift {U : Set ℂ}
    (hU : IsOpen U) (hsc : IsSimplyConnected U) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U)
    (hplus : ∀ z∈U, f z≠1) (hminus : ∀ z∈U, f z≠-1)
    {c : ℂ} (hc : c∈U) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧
      ‖g c‖≤Real.pi+‖f c‖ ∧ ∀ z∈U, Complex.cos (g z)=f z := by
  obtain ⟨G,hG,hcos⟩ := exists_analytic_cosine_lift hU hsc hf hplus hminus
  obtain ⟨n,hn⟩ := exists_cosine_period_translate_norm_le (G c)
  refine ⟨fun z => G z+(n:ℂ)*(2*Real.pi),hG.add analyticOnNhd_const,?_,?_⟩
  · simpa only [hcos c hc] using hn
  · intro z hz
    rw [Complex.cos_add_int_mul_two_pi,hcos z hz]

/-- The normalization used in the Schottky argument: f=cos(pi*g) and the
base value of g is controlled by the base value of f. -/
theorem exists_normalized_scaled_cosine_lift {U : Set ℂ}
    (hU : IsOpen U) (hsc : IsSimplyConnected U) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U)
    (hplus : ∀ z∈U, f z≠1) (hminus : ∀ z∈U, f z≠-1)
    {c : ℂ} (hc : c∈U) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧
      ‖g c‖≤1+‖f c‖/Real.pi ∧ ∀ z∈U, Complex.cos (Real.pi*g z)=f z := by
  obtain ⟨G,hG,hbase,hcos⟩ := exists_normalized_analytic_cosine_lift hU hsc hf hplus hminus hc
  have hp : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  refine ⟨fun z => G z/Real.pi,hG.div analyticOnNhd_const (fun _ _ => hp),?_,?_⟩
  · rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    calc
      ‖G c‖/Real.pi ≤ (Real.pi+‖f c‖)/Real.pi := div_le_div_of_nonneg_right hbase Real.pi_pos.le
      _ = 1+‖f c‖/Real.pi := by rw [add_div,div_self Real.pi_ne_zero]
  · intro z hz
    have heq : (Real.pi:ℂ)*(G z/Real.pi)=G z := by field_simp
    rw [heq,hcos z hz]

end FunctionTheory
