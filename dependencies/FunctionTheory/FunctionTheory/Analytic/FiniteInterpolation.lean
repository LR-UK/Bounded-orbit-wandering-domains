import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-!
# Finite analytic interpolation

Repeated divided differences split an analytic function into a polynomial and
an analytic remainder divisible by prescribed powers at finitely many points.
The neighbourhood need not be connected, and multiplicities can vary by point.
-/

open Filter Set Polynomial
open scoped Topology BigOperators

namespace FunctionTheory

set_option autoImplicit false

theorem analyticOnNhd_dslope {U : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (a : ℂ) :
    AnalyticOnNhd ℂ (dslope f a) U := by
  intro z hz
  by_cases hza : z = a
  · subst z
    obtain ⟨p, hp⟩ := hf a hz
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · have h : AnalyticAt ℂ (fun w => (f w - f a) / (w - a)) z :=
      ((hf z hz).sub analyticAt_const).div
      (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hza)
    apply h.congr
    filter_upwards [dslope_eventuallyEq_slope_of_ne f hza] with w hw
    simpa [slope, smul_eq_mul, div_eq_mul_inv, mul_comm] using hw.symm

/-- A finite Taylor division, with the remainder analytic on the same set. -/
theorem exists_polynomial_analytic_remainder_pow {U : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (a : ℂ) (m : ℕ) :
    ∃ (p : ℂ[X]) (g : ℂ → ℂ), AnalyticOnNhd ℂ g U ∧
      ∀ z, f z = p.eval z + (z - a) ^ m * g z := by
  induction m generalizing f with
  | zero => exact ⟨0, f, hf, by simp⟩
  | succ m ih =>
    obtain ⟨p, g, hg, hfg⟩ := ih (analyticOnNhd_dslope hf a)
    refine ⟨C (f a) + (X - C a) * p, g, hg, ?_⟩
    intro z
    have hs : (z - a) * dslope f a z = f z - f a := sub_smul_dslope f a z
    rw [hfg z] at hs
    simp only [eval_add, eval_C, eval_mul, eval_sub, eval_X, pow_succ]
    linear_combination -hs

/-- The polynomial imposing the chosen vanishing orders at the marked points. -/
noncomputable def vanishingPolynomial (s : Finset ℂ) (m : ℂ → ℕ) : ℂ[X] :=
  ∏ a ∈ s, (X - C a) ^ m a

/-- Analytic division by a polynomial with a prescribed finite zero divisor. -/
theorem exists_polynomial_analytic_remainder {U : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (s : Finset ℂ) (m : ℂ → ℕ) :
    ∃ (p : ℂ[X]) (g : ℂ → ℂ), AnalyticOnNhd ℂ g U ∧
      ∀ z, f z = p.eval z + (vanishingPolynomial s m).eval z * g z := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => exact ⟨0, f, hf, by simp [vanishingPolynomial]⟩
  | @insert a s ha ih =>
    obtain ⟨p, g, hg, hfg⟩ := exists_polynomial_analytic_remainder_pow hf a (m a)
    obtain ⟨q, h, hh, hgh⟩ := ih hg
    refine ⟨p + (X - C a) ^ m a * q, h, hh, ?_⟩
    intro z
    rw [hfg z, hgh z]
    simp only [vanishingPolynomial, Finset.prod_insert ha, eval_add, eval_mul,
      eval_pow, eval_sub, eval_X, eval_C]
    ring

/-- Divisibility by a power implies equality of all lower derivatives. -/
theorem iteratedDeriv_eq_of_sub_eq_pow_mul {f g h : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a) (hh : AnalyticAt ℂ h a)
    (heq : ∀ᶠ z in 𝓝 a, f z - g z = (z - a) ^ m * h z) :
    ∀ k < m, iteratedDeriv k f a = iteratedDeriv k g a := by
  have horder : (m : ℕ∞) ≤ analyticOrderAt (fun z => f z - g z) a :=
    (natCast_le_analyticOrderAt (hf.sub hg)).mpr
      ⟨h, hh, by simpa only [smul_eq_mul, Pi.sub_apply] using heq⟩
  intro k hk
  have hzero := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (hf.sub hg)).mp horder k hk
  rw [iteratedDeriv_sub hf.contDiffAt hg.contDiffAt] at hzero
  exact sub_eq_zero.mp hzero

/-- Multiplication by the vanishing polynomial preserves the prescribed jets. -/
theorem iteratedDeriv_eq_of_sub_eq_vanishingPolynomial_mul
    {f g h : ℂ → ℂ} {s : Finset ℂ} {m : ℂ → ℕ} {a : ℂ}
    (ha : a ∈ s) (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a)
    (hh : AnalyticAt ℂ h a)
    (heq : ∀ᶠ z in 𝓝 a,
      f z - g z = (vanishingPolynomial s m).eval z * h z) :
    ∀ k < m a, iteratedDeriv k f a = iteratedDeriv k g a := by
  classical
  apply iteratedDeriv_eq_of_sub_eq_pow_mul (h := fun z =>
    (vanishingPolynomial (s.erase a) m).eval z * h z) hf hg
    ((AnalyticOnNhd.eval_polynomial (vanishingPolynomial (s.erase a) m)
      a (mem_univ a)).mul hh)
  filter_upwards [heq] with z hz
  rw [hz]
  have hprod : vanishingPolynomial s m =
      (X - C a) ^ m a * vanishingPolynomial (s.erase a) m := by
    exact (Finset.mul_prod_erase s (fun b => (X - C b) ^ m b) ha).symm
  simp only [hprod, eval_mul, eval_pow, eval_sub, eval_X, eval_C, mul_assoc]

end FunctionTheory
