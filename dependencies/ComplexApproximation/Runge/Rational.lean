import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Field

/-!
# Rational functions without poles on a set

This representation records a denominator that is nonzero at every point of the
set. It is designed to turn finite Cauchy sums into the polynomial quotient
required by the Runge target.
-/

open Polynomial
open scoped BigOperators

namespace Runge

/-- A function agrees on `K` with a polynomial quotient whose denominator has no
zeros on `K`. Values outside `K` are unrestricted. -/
def IsRationalOn (K : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∃ p q : ℂ[X], (∀ z ∈ K, q.eval z ≠ 0) ∧
    ∀ z ∈ K, f z = p.eval z / q.eval z

namespace IsRationalOn

theorem polynomial (K : Set ℂ) (p : ℂ[X]) :
    IsRationalOn K (fun z => p.eval z) := by
  refine ⟨p, 1, ?_, ?_⟩ <;> simp

theorem const (K : Set ℂ) (c : ℂ) : IsRationalOn K (fun _ => c) := by
  simpa using polynomial K (C c)

theorem add {K : Set ℂ} {f g : ℂ → ℂ}
    (hf : IsRationalOn K f) (hg : IsRationalOn K g) :
    IsRationalOn K (fun z => f z + g z) := by
  obtain ⟨p, q, hq, hf⟩ := hf
  obtain ⟨r, s, hs, hg⟩ := hg
  refine ⟨p * s + q * r, q * s, ?_, ?_⟩
  · intro z hz
    simpa using mul_ne_zero (hq z hz) (hs z hz)
  · intro z hz
    simp only [Polynomial.eval_add, Polynomial.eval_mul]
    rw [hf z hz, hg z hz]
    exact div_add_div _ _ (hq z hz) (hs z hz)

theorem mul {K : Set ℂ} {f g : ℂ → ℂ}
    (hf : IsRationalOn K f) (hg : IsRationalOn K g) :
    IsRationalOn K (fun z => f z * g z) := by
  obtain ⟨p, q, hq, hf⟩ := hf
  obtain ⟨r, s, hs, hg⟩ := hg
  refine ⟨p * r, q * s, ?_, ?_⟩
  · intro z hz
    simpa using mul_ne_zero (hq z hz) (hs z hz)
  · intro z hz
    simp only [Polynomial.eval_mul]
    rw [hf z hz, hg z hz]
    exact div_mul_div_comm _ _ _ _

theorem sum {ι : Type*} {K : Set ℂ} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, IsRationalOn K (f i)) :
    IsRationalOn K (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const K 0
  | @insert i s hi ih =>
    have hfi := hf i (Finset.mem_insert_self i s)
    have hfs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using hfi.add hfs

theorem pow {K : Set ℂ} {f : ℂ → ℂ} (hf : IsRationalOn K f) (n : ℕ) :
    IsRationalOn K (fun z => f z ^ n) := by
  induction n with
  | zero => simpa using const K 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

/-- A simple pole outside `K` gives a rational function with no pole on `K`. -/
theorem simplePole {K : Set ℂ} {a : ℂ} (ha : a ∉ K) (c : ℂ) :
    IsRationalOn K (fun z => c / (z - a)) := by
  refine ⟨C c, X - C a, ?_, ?_⟩
  · intro z hz
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_ne_zero.mpr (fun h => ha (h ▸ hz))
  · intro z hz
    simp

end IsRationalOn

/-- Finite Cauchy sums have one polynomial denominator nonvanishing on `K`.
This is the algebraic conversion needed after discretising a Cauchy integral. -/
theorem exists_polynomials_sum_simplePoles {ι : Type*} (s : Finset ι)
    (K : Set ℂ) (a c : ι → ℂ) (ha : ∀ i ∈ s, a i ∉ K) :
    ∃ p q : ℂ[X], (∀ z ∈ K, q.eval z ≠ 0) ∧
      ∀ z ∈ K, (∑ i ∈ s, c i / (z - a i)) = p.eval z / q.eval z := by
  exact IsRationalOn.sum s (fun i z => c i / (z - a i))
    (fun i hi => IsRationalOn.simplePole (ha i hi) (c i))

end Runge
