import Runge.Holomorphic
import FunctionTheory.Analytic.FiniteInterpolation

/-!
# Runge approximation with finite jet interpolation

At each marked point `a`, the approximation preserves derivatives of orders
strictly below `m a`. The multiplicities may vary. The rational version also
retains a prescribed set of allowed poles. The functions are holomorphic on
an open neighbourhood of the compact approximation set.
-/

open Polynomial Set Filter FunctionTheory
open scoped Topology

namespace Runge

set_option autoImplicit false

private theorem polynomial_analyticAt (p : ℂ[X]) (z : ℂ) :
    AnalyticAt ℂ (fun w => p.eval w) z :=
  AnalyticOnNhd.eval_polynomial p z (mem_univ z)

/-- Rational Runge approximation retaining prescribed poles and finite jets. -/
theorem prescribed_poles_approximation_with_interpolation
    (K : Set ℂ) (hK : IsCompact K)
    (P : Set ℂ) (hP : MeetsBoundedComplementComponents K P)
    (U : Set ℂ) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (s : Finset ℂ) (hsK : ∀ a ∈ s, a ∈ K) (m : ℂ → ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z ∈ K, q.eval z ≠ 0) ∧
      (∀ a : ℂ, q.eval a = 0 → a ∈ P) ∧
      (∀ z ∈ K, ‖f z - p.eval z / q.eval z‖ < ε) ∧
      ∀ a ∈ s, ∀ k < m a,
        iteratedDeriv k f a = iteratedDeriv k (fun z => p.eval z / q.eval z) a := by
  obtain ⟨p, g, hg, hfg⟩ :=
    exists_polynomial_analytic_remainder (hf.analyticOnNhd hU) s m
  let d := vanishingPolynomial s m
  obtain ⟨B, hB, hbound⟩ :=
    (hK.image d.continuous).isBounded.exists_pos_norm_le
  obtain ⟨r, q, hq0, hqK, hqP, happrox⟩ := prescribed_poles_approximation
    K hK P hP U hU hKU g hg (ε / B) (div_pos hε hB)
  have hidentity (z : ℂ) (hqz : q.eval z ≠ 0) :
      f z - (p * q + d * r).eval z / q.eval z =
        d.eval z * (g z - r.eval z / q.eval z) := by
    rw [hfg z]
    simp only [eval_add, eval_mul]
    dsimp only [d]
    field_simp [hqz]
    ring
  refine ⟨p * q + d * r, q, hq0, hqK, hqP, ?_, ?_⟩
  · intro z hz
    rw [hidentity z (hqK z hz), norm_mul]
    calc
      ‖d.eval z‖ * ‖g z - r.eval z / q.eval z‖ ≤
          B * ‖g z - r.eval z / q.eval z‖ :=
        mul_le_mul_of_nonneg_right (hbound _ ⟨z, hz, rfl⟩) (norm_nonneg _)
      _ < B * (ε / B) := mul_lt_mul_of_pos_left (happrox z hz) hB
      _ = ε := mul_div_cancel₀ ε hB.ne'
  · intro a ha
    have hqa := hqK a (hsK a ha)
    apply iteratedDeriv_eq_of_sub_eq_vanishingPolynomial_mul ha
      (hf.analyticOnNhd hU a (hKU (hsK a ha)))
      ((polynomial_analyticAt _ a).div (polynomial_analyticAt q a) hqa)
      ((hg a (hKU (hsK a ha))).sub
        ((polynomial_analyticAt r a).div (polynomial_analyticAt q a) hqa))
    filter_upwards [q.continuous.continuousAt.eventually_ne hqa] with z hz
    exact hidentity z hz

/-- Polynomial Runge approximation with arbitrary finite interpolation orders. -/
theorem polynomial_approximation_with_interpolation
    (K : Set ℂ) (hK : IsCompact K) (hconn : IsConnected Kᶜ)
    (U : Set ℂ) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (s : Finset ℂ) (hsK : ∀ a ∈ s, a ∈ K) (m : ℂ → ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℂ[X], (∀ z ∈ K, ‖f z - p.eval z‖ < ε) ∧
      ∀ a ∈ s, ∀ k < m a,
        iteratedDeriv k f a = iteratedDeriv k (fun z => p.eval z) a := by
  obtain ⟨p, g, hg, hfg⟩ :=
    exists_polynomial_analytic_remainder (hf.analyticOnNhd hU) s m
  let d := vanishingPolynomial s m
  obtain ⟨B, hB, hbound⟩ :=
    (hK.image d.continuous).isBounded.exists_pos_norm_le
  obtain ⟨r, happrox⟩ := polynomial_approximation K hK hconn U hU hKU g hg
    (ε / B) (div_pos hε hB)
  have hidentity (z : ℂ) : f z - (p + d * r).eval z = d.eval z * (g z - r.eval z) := by
    rw [hfg z]
    simp only [eval_add, eval_mul]
    dsimp only [d]
    ring
  refine ⟨p + d * r, ?_, ?_⟩
  · intro z hz
    rw [hidentity z, norm_mul]
    calc
      ‖d.eval z‖ * ‖g z - r.eval z‖ ≤ B * ‖g z - r.eval z‖ :=
        mul_le_mul_of_nonneg_right (hbound _ ⟨z, hz, rfl⟩) (norm_nonneg _)
      _ < B * (ε / B) := mul_lt_mul_of_pos_left (happrox z hz) hB
      _ = ε := mul_div_cancel₀ ε hB.ne'
  · intro a ha
    exact iteratedDeriv_eq_of_sub_eq_vanishingPolynomial_mul ha
      (hf.analyticOnNhd hU a (hKU (hsK a ha))) (polynomial_analyticAt _ a)
      ((hg a (hKU (hsK a ha))).sub (polynomial_analyticAt r a))
      (Eventually.of_forall hidentity)

/-- Rational approximation on an arbitrary compact set, retaining finite jets. -/
theorem rational_approximation_with_interpolation
    (K : Set ℂ) (hK : IsCompact K)
    (U : Set ℂ) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (s : Finset ℂ) (hsK : ∀ a ∈ s, a ∈ K) (m : ℂ → ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z ∈ K, q.eval z ≠ 0) ∧
      (∀ z ∈ K, ‖f z - p.eval z / q.eval z‖ < ε) ∧
      ∀ a ∈ s, ∀ k < m a,
        iteratedDeriv k f a = iteratedDeriv k (fun z => p.eval z / q.eval z) a := by
  have hP : MeetsBoundedComplementComponents K univ := by
    intro a ha _
    exact ⟨a, mem_connectedComponentIn ha, mem_univ a⟩
  obtain ⟨p, q, hq0, hqK, _, herr, hjet⟩ :=
    prescribed_poles_approximation_with_interpolation K hK univ hP
      U hU hKU f hf s hsK m ε hε
  exact ⟨p, q, hq0, hqK, herr, hjet⟩

end Runge
