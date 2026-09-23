import FunctionTheory.Topology.FiniteComposition
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Set Filter Function
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- The degree of a prefix of a sequence of monomials. -/
def monomialPrefixDegree (d : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => monomialPrefixDegree d n * d n

/-- The leading coefficient of a prefix of a sequence of monomials. -/
def monomialPrefixCoefficient (a : ℕ → ℂ) (d : ℕ → ℕ) : ℕ → ℂ
  | 0 => 1
  | n+1 => a n * monomialPrefixCoefficient a d n ^ d n

/-- Composition retains the monomial form, with the product of the degrees. -/
theorem finiteComposition_monomials (a : ℕ → ℂ) (d : ℕ → ℕ) (n : ℕ) (z : ℂ) :
    finiteComposition (fun k z => a k * z ^ d k) n z =
      monomialPrefixCoefficient a d n * z ^ monomialPrefixDegree d n := by
  induction n with
  | zero => simp [finiteComposition,monomialPrefixDegree,monomialPrefixCoefficient]
  | succ n ih =>
    simp only [finiteComposition,comp_apply,ih,monomialPrefixDegree,
      monomialPrefixCoefficient,mul_pow,pow_mul,mul_assoc]

/-- Degrees at least two force prefix degrees to grow without bound. -/
theorem monomialPrefixDegree_ge (d : ℕ → ℕ) (hd : ∀ n, 2≤d n) (n : ℕ) :
    n+1≤monomialPrefixDegree d n := by
  induction n with
  | zero => simp [monomialPrefixDegree]
  | succ n ih =>
    change n+1+1≤monomialPrefixDegree d n*d n
    have H := Nat.mul_le_mul ih (hd n)
    nlinarith

theorem monomialPrefixDegree_tendsto (d : ℕ → ℕ) (hd : ∀ n, 2≤d n) :
    Tendsto (monomialPrefixDegree d) atTop atTop := by
  exact tendsto_atTop_mono (fun n => (Nat.le_succ n).trans
    (monomialPrefixDegree_ge d hd n)) tendsto_id

/-- The positive elementary rotation of order N. At N=0 the total
representative has value one; all uses of its order require N positive. -/
noncomputable def elementaryRootRotation (N : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / N)

theorem elementaryRootRotation_pow {N : ℕ} (hN : N≠0) :
    elementaryRootRotation N ^ N=1 := by
  rw [elementaryRootRotation,← Complex.exp_nat_mul]
  convert Complex.exp_two_pi_mul_I using 1
  congr 1
  field_simp

theorem elementaryRootRotation_ne_one {N : ℕ} (hN : 1<N) :
    elementaryRootRotation N≠1 := by
  have H := Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k:=1) (by omega : N≠0)
  simp only [Nat.cast_one,mul_one] at H
  intro h
  have hdiv : N∣1 := H.mp h
  exact (not_le_of_gt hN) (Nat.le_of_dvd (by omega) hdiv)

theorem elementaryRootRotation_norm (N : ℕ) : ‖elementaryRootRotation N‖=1 := by
  simp [elementaryRootRotation,Complex.norm_exp,Complex.div_re]

theorem elementaryRootRotation_tendsto :
    Tendsto elementaryRootRotation atTop (𝓝 1) := by
  have H := Complex.continuous_exp.continuousAt.tendsto.comp
    (tendsto_const_div_atTop_nhds_zero_nat (2 * Real.pi * Complex.I))
  change Tendsto (fun n : ℕ => Complex.exp (2 * Real.pi * Complex.I / n)) atTop (𝓝 1)
  simpa only [Complex.exp_zero,Function.comp_def] using H

/-- Rotation through the reciprocal of the product degree leaves the whole
prefix unchanged, even when the monomials have arbitrary coefficients. -/
theorem finiteComposition_monomials_rotation (a : ℕ → ℂ) (d : ℕ → ℕ)
    (n : ℕ) (hD : monomialPrefixDegree d n≠0) (z : ℂ) :
    finiteComposition (fun k z => a k * z^d k) n
      (elementaryRootRotation (monomialPrefixDegree d n)*z) =
      finiteComposition (fun k z => a k * z^d k) n z := by
  rw [finiteComposition_monomials,finiteComposition_monomials,mul_pow,
    elementaryRootRotation_pow hD,one_mul]

end FunctionTheory
