import FunctionTheory.Conformal.BlaschkeBoundaryDerivative
import FunctionTheory.Conformal.UnicriticalQuotient
import FunctionTheory.Conformal.ProperDiscBlaschke
import FunctionTheory.Conformal.BlaschkeProper

open Set Metric Filter
open scoped Topology BigOperators
namespace FunctionTheory
set_option autoImplicit false

namespace FiniteBlaschkeProduct

/-- If a finite Blaschke product fixes zero and has no other critical point,
all of its zeros are zero. The proof uses the positive real part of the
holomorphic representative of `B/(z*B')`, not a critical-point count. -/
theorem zeros_eq_zero_of_unicritical (B : FiniteBlaschkeProduct)
    (hB0 : B.eval 0=0)
    (hcrit : ∀ z∈ball (0:ℂ) 1, z≠0 → deriv B.eval z≠0) :
    ∀ i, B.zero i=0 := by
  have hmap : MapsTo B.eval (ball (0:ℂ) 1) (ball (0:ℂ) 1) :=
    fun z hz => mem_ball_zero_iff.mpr (B.norm_eval_lt_one (mem_ball_zero_iff.mp hz))
  have ho : meromorphicOrderAt B.eval 0≠⊤ :=
    order_ne_top_of_isProperMap_holomorphic_disc
      (B.analyticOnNhd_closedBall.mono ball_subset_closedBall) hmap B.isProperMap_discMap
      0 (mem_ball_self one_pos)
  have hcritK : ∀ z∈closedBall (0:ℂ) 1, z≠0 → deriv B.eval z≠0 := by
    intro z hz hn
    rcases (mem_closedBall_zero_iff.mp hz).lt_or_eq with H|H
    · exact hcrit z (mem_ball_zero_iff.mpr H) hn
    · exact B.deriv_ne_zero_on_circle H
  obtain ⟨g,hg,hgeq⟩ := exists_analytic_quotient_by_mul_deriv B.analyticOnNhd_closedBall hB0 ho hcritK
  have hcircle : ∀ z : ℂ, ‖z‖=1 → 0<(g z).re := by
    intro z hz
    have hz0 : z≠0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
    rw [hgeq z (mem_closedBall_zero_iff.mpr hz.le) hz0]
    have Hquot : B.eval z/(z*deriv B.eval z)=(z*logDeriv B.eval z)⁻¹ := by
      simp only [logDeriv_apply,div_eq_mul_inv,mul_inv_rev,inv_inv]
      ring
    rw [Hquot,Complex.inv_re]
    apply div_pos (B.re_mul_logDeriv_pos_on_circle hz)
    apply Complex.normSq_pos.mpr
    intro H
    have Hp := B.re_mul_logDeriv_pos_on_circle hz
    rw [H,Complex.zero_re] at Hp
    exact Hp.false
  have hpos := re_pos_on_closedDisc_of_re_pos_on_circle hg hcircle
  intro i
  by_contra hn
  have hz : B.zero i∈closedBall (0:ℂ) 1 := mem_closedBall_zero_iff.mpr (B.zero_lt_one i).le
  have H := hpos (B.zero i) hz
  rw [hgeq (B.zero i) hz hn,B.eval_zero i,zero_div,Complex.zero_re] at H
  exact H.false

/-- A finite Blaschke product fixing its only possible critical point at
zero is a unimodular monomial. Degree one is allowed in this formulation. -/
theorem eval_eq_monomial_of_unicritical (B : FiniteBlaschkeProduct)
    (hB0 : B.eval 0=0)
    (hcrit : ∀ z∈ball (0:ℂ) 1, z≠0 → deriv B.eval z≠0) (z : ℂ) :
    B.eval z=B.phase*z^(B.degreePred+1) := by
  have H := B.zeros_eq_zero_of_unicritical hB0 hcrit
  simp [eval,H,blaschkeFactor]

end FiniteBlaschkeProduct

/-- A proper holomorphic disc map that fixes its unique critical point at
zero is a unimodular monomial of degree at least two. The original map
need only be holomorphic on the open disc. -/
theorem exists_monomial_of_isProperMap_unicritical_disc
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball (0:ℂ) 1))
    (hmap : MapsTo f (ball (0:ℂ) 1) (ball (0:ℂ) 1))
    (hproper : IsProperMap (fun z : ball (0:ℂ) 1 =>
      (⟨f z,hmap z.property⟩ : ball (0:ℂ) 1)))
    (hf0 : f 0=0) (hd0 : deriv f 0=0)
    (hcrit : ∀ z∈ball (0:ℂ) 1, z≠0 → deriv f z≠0) :
    ∃ (d : ℕ) (c : ℂ), 2≤d ∧ ‖c‖=1 ∧
      EqOn f (fun z => c*z^d) (ball (0:ℂ) 1) := by
  obtain ⟨B,hB⟩ := exists_finiteBlaschkeProduct_of_isProperMap_holomorphic_disc hf hmap hproper
  have hderiv : ∀ z∈ball (0:ℂ) 1, deriv f z=deriv B.eval z := by
    intro z hz
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact hB hw
  have hB0 : B.eval 0=0 := (hB (mem_ball_self one_pos)).symm.trans hf0
  have hcritB : ∀ z∈ball (0:ℂ) 1, z≠0 → deriv B.eval z≠0 := by
    intro z hz hn
    rw [← hderiv z hz]
    exact hcrit z hz hn
  have Hmono : B.eval=(fun z => B.phase*z^(B.degreePred+1)) :=
    funext (B.eval_eq_monomial_of_unicritical hB0 hcritB)
  have hk : 0<B.degreePred := by
    by_contra H
    have hk0 : B.degreePred=0 := Nat.eq_zero_of_not_pos H
    have HD : deriv B.eval 0=0 := (hderiv 0 (mem_ball_self one_pos)).symm.trans hd0
    rw [Hmono,hk0] at HD
    simp only [zero_add,pow_one] at HD
    have Hphase : B.phase=0 := by simpa using HD
    have Hnorm := B.norm_phase
    rw [Hphase,norm_zero] at Hnorm
    norm_num at Hnorm
  refine ⟨B.degreePred+1,B.phase,by omega,B.norm_phase,?_⟩
  intro z hz
  rw [hB hz,Hmono]

end FunctionTheory
