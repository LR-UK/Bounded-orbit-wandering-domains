import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Basic
import Runge.Holomorphic

/-!
# Original target statements, now proved

This compatibility module checks that the completed development proves the
original rational and polynomial statements and the prescribed-pole form.
-/

open Polynomial

namespace RungeTargets

/-- First milestone: rational approximation with no poles on the compact set.
This is the mathematical statement of the public `runge_theorem` challenge. -/
theorem rational_approximation (K : Set ℂ) (hK : IsCompact K)
    (U : Set ℂ) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : ℂ[X], (∀ z ∈ K, q.eval z ≠ 0) ∧
      (∀ z ∈ K, ‖f z - p.eval z / q.eval z‖ < ε) := by
  exact Runge.rational_approximation K hK U hU hKU f hf ε hε

/-- Polynomial approximation when the complement is connected. -/
theorem polynomial_approximation (K : Set ℂ) (hK : IsCompact K)
    (hconn : IsConnected Kᶜ) (U : Set ℂ) (hU : IsOpen U)
    (hKU : K ⊆ U) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  exact Runge.polynomial_approximation K hK hconn U hU hKU f hf ε hε

/-- Prescribed-pole form, with the component hypothesis expanded explicitly. -/
theorem prescribed_poles_approximation (K : Set ℂ) (hK : IsCompact K) (P : Set ℂ)
    (hP : ∀ a ∉ K, Bornology.IsBounded (connectedComponentIn Kᶜ a) →
      (connectedComponentIn Kᶜ a ∩ P).Nonempty)
    (U : Set ℂ) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z ∈ K, q.eval z ≠ 0) ∧
      (∀ a : ℂ, q.eval a = 0 → a ∈ P) ∧
      ∀ z ∈ K, ‖f z - p.eval z / q.eval z‖ < ε := by
  exact Runge.prescribed_poles_approximation K hK P hP U hU hKU f hf ε hε

end RungeTargets
