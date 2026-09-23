import FunctionTheory.Conformal.BlaschkeDiscMap
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

open Set Metric
open scoped Topology

namespace FunctionTheory.FiniteBlaschkeProduct

set_option autoImplicit false

/-- A unimodular multiple of a positive power, as a finite Blaschke product. -/
def monomial (degreePred : ℕ) (a : ℂ) (ha : ‖a‖=1) : FiniteBlaschkeProduct where
  degreePred := degreePred
  zero := fun _ => 0
  zero_lt_one := fun _ => by simp
  phase := a
  norm_phase := ha

@[simp] theorem eval_monomial (k : ℕ) (a : ℂ) (ha : ‖a‖=1) (z : ℂ) :
    (monomial k a ha).eval z=a*z^(k+1) := by
  change a*(∏ i : Fin (k+1), blaschkeFactor 0 z)=a*z^(k+1)
  simp [blaschkeFactor]

/-- A monomial Blaschke product has precisely one preimage of zero. -/
theorem monomial_eval_eq_zero_iff (k : ℕ) (a : ℂ) (ha : ‖a‖=1) (z : ℂ) :
    (monomial k a ha).eval z=0 ↔ z=0 := by
  have ha0 : a≠0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  simp [eval_monomial,mul_eq_zero,ha0]

theorem deriv_monomial (k : ℕ) (a : ℂ) (ha : ‖a‖=1) (z : ℂ) :
    deriv (monomial k a ha).eval z=a*((k+1:ℕ):ℂ)*z^k := by
  have hf : (monomial k a ha).eval=(fun z => a*z^(k+1)) := funext (eval_monomial k a ha)
  rw [hf]
  simpa [mul_assoc] using ((hasDerivAt_pow (k+1) z).const_mul a).deriv

/-- For degree at least two the only critical point is the origin. -/
theorem deriv_monomial_eq_zero_iff {k : ℕ} (hk : 0<k)
    (a : ℂ) (ha : ‖a‖=1) (z : ℂ) :
    deriv (monomial k a ha).eval z=0 ↔ z=0 := by
  have ha0 : a≠0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  rw [deriv_monomial]
  have hd0 : ((k+1:ℕ):ℂ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [mul_eq_zero,ha0,hd0,false_or,pow_eq_zero_iff (Nat.ne_of_gt hk)]

end FunctionTheory.FiniteBlaschkeProduct
