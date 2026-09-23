import FunctionTheory.Conformal.FiniteBlaschke
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Tactic

open Set Metric
open scoped Topology BigOperators ComplexConjugate
namespace FunctionTheory
set_option autoImplicit false

theorem analyticAt_blaschkeFactor_of_norm_le_one {a z : ℂ}
    (ha : ‖a‖<1) (hz : ‖z‖≤1) : AnalyticAt ℂ (blaschkeFactor a) z :=
  (analyticAt_id.sub analyticAt_const).div
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
    (blaschke_denominator_ne_zero ha hz)

/-- The boundary logarithmic derivative of a Blaschke factor is a positive
Poisson kernel. -/
theorem mul_logDeriv_blaschkeFactor_on_circle {a z : ℂ}
    (ha : ‖a‖<1) (hz : ‖z‖=1) :
    z*logDeriv (blaschkeFactor a) z=(((1-‖a‖^2)/‖z-a‖^2:ℝ):ℂ) := by
  have hd := blaschke_denominator_ne_zero ha hz.le
  have hz0 : z≠0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  have hza : z-a≠0 := by
    intro H
    have H' := sub_eq_zero.mp H
    rw [← H',hz] at ha
    exact ha.false
  have hzz : z*conj z=1 := by rw [Complex.mul_conj',hz]; norm_num
  have hden : 1-conj a*z=z*conj (z-a) := by
    rw [map_sub,mul_sub,hzz]
    ring
  have hderiv := ((hasDerivAt_id z).sub_const a).div
    ((hasDerivAt_const z (1:ℂ)).sub ((hasDerivAt_id z).const_mul (conj a))) hd
  simp only [id_eq,Pi.sub_apply,mul_one,one_mul,zero_sub] at hderiv
  change HasDerivAt (fun w : ℂ => (w-a)/(1-conj a*w))
    (((1-conj a*z)-(z-a)*(-conj a))/(1-conj a*z)^2) z at hderiv
  have H : z*logDeriv (blaschkeFactor a) z=
      (1-conj a*a)/((z-a)*conj (z-a)) := by
    rw [logDeriv_apply]
    change z*(deriv (fun w => (w-a)/(1-conj a*w)) z / ((z-a)/(1-conj a*z)))=_
    rw [hderiv.deriv]
    rw [hden]
    have hconj : conj (z-a)≠0 := (map_ne_zero (starRingEnd ℂ)).mpr hza
    field_simp
    linear_combination -hden
  rw [H,mul_comm (conj a) a,Complex.mul_conj',Complex.mul_conj']
  push_cast
  rfl

namespace FiniteBlaschkeProduct

/-- The logarithmic derivative of a positive-degree finite Blaschke product
on the circle is the sum of the individual Poisson kernels. -/
theorem mul_logDeriv_on_circle (B : FiniteBlaschkeProduct) {z : ℂ} (hz : ‖z‖=1) :
    z*logDeriv B.eval z=
      ((∑ i : Fin (B.degreePred+1), (1-‖B.zero i‖^2)/‖z-B.zero i‖^2 : ℝ):ℂ) := by
  have hn : ∀ i : Fin (B.degreePred+1), blaschkeFactor (B.zero i) z≠0 := by
    intro i
    apply norm_ne_zero_iff.mp
    rw [norm_blaschkeFactor_eq_one (B.zero_lt_one i) hz]
    norm_num
  have hd : ∀ i : Fin (B.degreePred+1), DifferentiableAt ℂ (blaschkeFactor (B.zero i)) z :=
    fun i => (analyticAt_blaschkeFactor_of_norm_le_one (B.zero_lt_one i) hz.le).differentiableAt
  have hp : B.phase≠0 := norm_ne_zero_iff.mp (by rw [B.norm_phase]; norm_num)
  change z*logDeriv (fun w => B.phase*∏ i, blaschkeFactor (B.zero i) w) z=_
  rw [logDeriv_const_mul z B.phase hp,logDeriv_fun_prod (fun i _ => hn i) (fun i _ => hd i)]
  rw [Finset.mul_sum]
  simp only [mul_logDeriv_blaschkeFactor_on_circle (B.zero_lt_one _) hz,Complex.ofReal_sum]

/-- Finite Blaschke products have strictly positive angular derivative on
the unit circle. -/
theorem re_mul_logDeriv_pos_on_circle (B : FiniteBlaschkeProduct) {z : ℂ} (hz : ‖z‖=1) :
    0<(z*logDeriv B.eval z).re := by
  rw [B.mul_logDeriv_on_circle hz,Complex.ofReal_re]
  apply Finset.sum_pos
  · intro i hi
    apply div_pos
    · nlinarith [B.zero_lt_one i,norm_nonneg (B.zero i)]
    · apply sq_pos_of_pos
      apply norm_pos_iff.mpr
      intro H
      have H' := sub_eq_zero.mp H
      have hi := B.zero_lt_one i
      rw [← H',hz] at hi
      exact hi.false
  · exact Finset.univ_nonempty

/-- No critical point of a finite Blaschke product lies on the unit circle. -/
theorem deriv_ne_zero_on_circle (B : FiniteBlaschkeProduct) {z : ℂ} (hz : ‖z‖=1) :
    deriv B.eval z≠0 := by
  intro H
  have hp := B.re_mul_logDeriv_pos_on_circle hz
  simp only [logDeriv_apply,H,zero_div,mul_zero,Complex.zero_re,lt_self_iff_false] at hp

end FiniteBlaschkeProduct
end FunctionTheory
