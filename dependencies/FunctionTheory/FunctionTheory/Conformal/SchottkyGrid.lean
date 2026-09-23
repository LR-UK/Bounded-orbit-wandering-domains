import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

open Set Metric
namespace FunctionTheory
set_option autoImplicit false

/-- A coarse bound on the gaps between the inverse hyperbolic cosines of
successive positive integers. No optimal constant is needed for Schottky. -/
theorem arcosh_add_one_le {x : ℝ} (hx : 1≤x) :
    Real.arcosh (x+1) ≤ Real.arcosh x+2 := by
  have h2 : 2≤Real.cosh 2 := by
    have H := Real.cosh_two_mul (1:ℝ)
    norm_num at H
    have hs : 1≤Real.sinh 1 := Real.self_le_sinh_iff.mpr (by norm_num)
    nlinarith [Real.one_le_cosh 1]
  have ha := Real.arcosh_nonneg hx
  have hs : 0≤Real.sinh (Real.arcosh x)*Real.sinh 2 :=
    mul_nonneg (Real.sinh_nonneg_iff.mpr ha) (Real.sinh_nonneg_iff.mpr (by norm_num))
  have hc : x+1≤Real.cosh (Real.arcosh x+2) := by
    rw [Real.cosh_add,Real.cosh_arcosh hx]
    nlinarith
  have H := (Real.arcosh_le_arcosh (by linarith : 0<x+1)
    (Real.cosh_pos (Real.arcosh x+2))).mpr hc
  rwa [Real.arcosh_cosh (by linarith)] at H

/-- Every height is within one unit of a height whose hyperbolic cosine,
after scaling by pi, is a positive integer. -/
theorem exists_nearby_integer_cosh (y : ℝ) :
    ∃ n : ℕ, 1≤n ∧ ∃ v : ℝ, |v-y|<1 ∧ Real.cosh (Real.pi*v)=n := by
  let t := Real.pi*|y|
  have ht : 0≤t := mul_nonneg Real.pi_pos.le (abs_nonneg y)
  let n := ⌊Real.cosh t⌋₊
  have hn : 1≤n := (Nat.one_le_floor_iff _).mpr (Real.one_le_cosh t)
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hlo : Real.arcosh (n:ℝ)≤t := by
    have H := (Real.arcosh_le_arcosh (by linarith : 0<(n:ℝ)) (Real.cosh_pos t)).mpr
      (Nat.floor_le (Real.cosh_pos t).le)
    simpa only [Real.arcosh_cosh ht] using H
  have hhi : t<Real.arcosh (n:ℝ)+2 := by
    have H := (Real.arcosh_lt_arcosh (Real.cosh_pos t) (by linarith : 0<(n:ℝ)+1)).mpr
      (Nat.lt_floor_add_one (Real.cosh t))
    rw [Real.arcosh_cosh ht] at H
    exact H.trans_le (arcosh_add_one_le hnR)
  have hgap : |Real.arcosh (n:ℝ)/Real.pi - (|y|)|<1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr ((div_le_iff₀ Real.pi_pos).mpr (by simpa [t,mul_comm] using hlo)))]
    have H : |y|-Real.arcosh (n:ℝ)/Real.pi<2/Real.pi := by
      apply (lt_div_iff₀ Real.pi_pos).mpr
      have heq : (|y|-Real.arcosh (n:ℝ)/Real.pi)*Real.pi=t-Real.arcosh (n:ℝ) := by
        dsimp [t]
        field_simp
      rw [heq]
      linarith
    have hp : (2:ℝ)/Real.pi<1 := (div_lt_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
    linarith
  refine ⟨n,hn,?_⟩
  by_cases hy : 0≤y
  · refine ⟨Real.arcosh (n:ℝ)/Real.pi,?_,?_⟩
    · simpa only [abs_of_nonneg hy] using hgap
    · rw [mul_div_cancel₀ _ Real.pi_ne_zero,Real.cosh_arcosh hnR]
  · have hy' : y≤0 := le_of_not_ge hy
    refine ⟨-(Real.arcosh (n:ℝ)/Real.pi),?_,?_⟩
    · have heq : -(Real.arcosh (n:ℝ)/Real.pi)-y=-(Real.arcosh (n:ℝ)/Real.pi - (|y|)) := by
        rw [abs_of_nonpos hy']; ring
      rw [heq,abs_neg]
      exact hgap
    · rw [mul_neg,Real.cosh_neg,mul_div_cancel₀ _ Real.pi_ne_zero,Real.cosh_arcosh hnR]

/-- The inverse image of the positive integers under the scaled cosine
meets every complex disc of radius three. -/
theorem exists_nearby_integer_cosine (b : ℂ) :
    ∃ a : ℂ, dist a b<3 ∧ ∃ n : ℕ, 1≤n ∧ Complex.cos (Real.pi*a)=n := by
  obtain ⟨n,hn,v,hv,hcosh⟩ := exists_nearby_integer_cosh b.im
  let m : ℤ := ⌊b.re/2⌋
  let a : ℂ := 2*(m:ℂ)+(v:ℂ)*Complex.I
  have hmlo : 2*(m:ℝ)≤b.re := by
    have H := Int.floor_le (b.re/2)
    dsimp [m]
    linarith
  have hmhi : b.re-2*(m:ℝ)<2 := by
    have H := Int.lt_floor_add_one (b.re/2)
    dsimp [m]
    linarith
  have hreal : |(a-b).re|<2 := by
    have heq : (a-b).re=2*(m:ℝ)-b.re := by simp [a]
    rw [heq,abs_of_nonpos (sub_nonpos.mpr hmlo)]
    linarith
  have himag : |(a-b).im|<1 := by simpa [a] using hv
  refine ⟨a,?_,n,hn,?_⟩
  · rw [dist_eq_norm]
    exact (Complex.norm_le_abs_re_add_abs_im (a-b)).trans_lt (by linarith)
  · have heq : (Real.pi:ℂ)*a=((Real.pi*v:ℝ):ℂ)*Complex.I+(m:ℂ)*(2*Real.pi) := by
      simp only [a,Complex.ofReal_mul]
      ring
    rw [heq,Complex.cos_add_int_mul_two_pi,Complex.cos_mul_I,← Complex.ofReal_cosh,hcosh]
    norm_cast

/-- A double cosine lift of a function omitting both critical values has
an omitted value in every target disc of radius three. -/
theorem no_ball_subset_double_cosine_lift_image {U : Set ℂ} {f g : ℂ → ℂ}
    (hplus : ∀ z∈U, f z≠1) (hminus : ∀ z∈U, f z≠-1)
    (hcos : ∀ z∈U, Complex.cos (Real.pi*Complex.cos (Real.pi*g z))=f z) :
    ∀ b : ℂ, ¬ ball b 3 ⊆ g '' U := by
  intro b hsub
  obtain ⟨a,ha,n,hn,hna⟩ := exists_nearby_integer_cosine b
  obtain ⟨z,hz,hzval⟩ := hsub (mem_ball.mpr ha)
  have hval : f z=Complex.cos ((n:ℂ)*Real.pi) := by
    rw [← hcos z hz,hzval,hna,mul_comm]
  have hsq : (f z)^2=1 := by
    rw [hval]
    have H := Complex.sin_sq_add_cos_sq ((n:ℂ)*Real.pi)
    simpa only [Complex.sin_nat_mul_pi,zero_pow (by decide : 2≠0),zero_add] using H
  have hfac : (f z-1)*(f z+1)=0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exact hplus z hz (sub_eq_zero.mp h)
  · exact hminus z hz (eq_neg_of_add_eq_zero_left h)

end FunctionTheory
