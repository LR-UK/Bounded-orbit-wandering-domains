import FunctionTheory.Analytic.FiniteInterpolation
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Topology.DiscreteSubset

open Set Filter Polynomial
open scoped Topology BigOperators

namespace FunctionTheory

set_option autoImplicit false

/-- On a compact set, multiplication by a polynomial whose zeros are confined to
singular points makes a meromorphic function analytic. -/
theorem exists_polynomial_clearing_singularities {K : Set ℂ} (hK : IsCompact K)
    {f : ℂ → ℂ} (hf : MeromorphicOn f K) :
    ∃ (s : Finset ℂ) (m : ℂ → ℕ),
      let q := vanishingPolynomial s m
      q ≠ 0 ∧
      (∀ a, q.eval a = 0 → a ∈ K ∧ ¬ AnalyticAt ℂ f a) ∧
      AnalyticOnNhd ℂ (fun z => q.eval z * f z) K := by
  classical
  have hs := hK.finite_sdiff_of_mem_codiscreteWithin
    (MeromorphicOn.eventually_codiscreteWithin_analyticAt f hf)
  let s := hs.toFinset
  have hsmem (a : ℂ) : a ∈ s ↔ a ∈ K ∧ ¬ AnalyticAt ℂ f a := by
    simp [s]
  have hpow : ∀ a : ℂ, ∃ m : ℕ,
      a ∈ K → AnalyticAt ℂ (fun z => (z - a) ^ m * f z) a := by
    intro a
    by_cases ha : a ∈ K
    · obtain ⟨n, hn⟩ := hf a ha
      exact ⟨n, fun _ => by simpa only [smul_eq_mul] using hn⟩
    · exact ⟨0, fun h => False.elim (ha h)⟩
  choose m hm using hpow
  let q := vanishingPolynomial s m
  have hq : q ≠ 0 := by
    simp [q, vanishingPolynomial, Finset.prod_ne_zero_iff, X_sub_C_ne_zero]
  have hqaway : ∀ a ∉ s, q.eval a ≠ 0 := by
    intro a ha
    simp only [q, vanishingPolynomial, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro b hb
    apply pow_ne_zero
    exact sub_ne_zero.mpr (fun h => ha (h ▸ hb))
  refine ⟨s, m, hq, ?_, ?_⟩
  · intro a ha
    apply (hsmem a).mp
    by_contra hn
    exact hqaway a hn ha
  · intro a haK
    by_cases ha : a ∈ s
    · let r := vanishingPolynomial (s.erase a) m
      have hsplit : q = (X - C a) ^ m a * r := by
        exact (Finset.mul_prod_erase s (fun b => (X - C b) ^ m b) ha).symm
      have hfun : (fun z => q.eval z * f z) =
          fun z => r.eval z * ((z - a) ^ m a * f z) := by
        funext z
        rw [hsplit]
        simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C]
        ring
      rw [hfun]
      exact (AnalyticOnNhd.eval_polynomial r a (mem_univ a)).mul (hm a haK)
    · have hfa : AnalyticAt ℂ f a := by
        by_contra hn
        exact ha ((hsmem a).mpr ⟨haK, hn⟩)
      exact (AnalyticOnNhd.eval_polynomial q a (mem_univ a)).mul hfa

/-- A meromorphic function near a compact set is a rational function plus an
analytic remainder, with denominator zeros only at singular points in that set.
The equality is asserted away from those denominator zeros. -/
theorem exists_rational_analytic_remainder {K : Set ℂ} (hK : IsCompact K)
    {f : ℂ → ℂ} (hf : MeromorphicOn f K) :
    ∃ (p q : ℂ[X]) (g : ℂ → ℂ), q ≠ 0 ∧
      (∀ a, q.eval a = 0 → a ∈ K ∧ ¬ AnalyticAt ℂ f a) ∧
      AnalyticOnNhd ℂ g K ∧
      ∀ z, q.eval z ≠ 0 → f z = p.eval z / q.eval z + g z := by
  classical
  obtain ⟨s, m, hq, hqsing, hF⟩ := exists_polynomial_clearing_singularities hK hf
  let q := vanishingPolynomial s m
  -- Divide the cleared numerator by the same finite vanishing polynomial.

  have hsplit : ∃ (p : ℂ[X]) (g : ℂ → ℂ), AnalyticOnNhd ℂ g K ∧
      ∀ z, q.eval z * f z = p.eval z + q.eval z * g z := by
    exact exists_polynomial_analytic_remainder hF s m
  obtain ⟨p, g, hg, hidentity⟩ := hsplit
  refine ⟨p, q, g, hq, hqsing, hg, ?_⟩
  intro z hz
  have heq := hidentity z
  field_simp [hz]
  linear_combination heq

end FunctionTheory
