import Runge.PrescribedPoles

/-!
# Runge's theorem stated using complex differentiability

On an open subset of the complex plane, complex differentiability implies
analyticity. These interfaces express the three Runge results directly in the
usual holomorphic-function hypothesis.
-/

open Polynomial

namespace Runge

theorem rational_approximation_of_holomorphic (K : Set ℂ) (hK : IsCompact K)
    (U : Set ℂ) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : ℂ[X], (∀ z ∈ K, q.eval z ≠ 0) ∧
      ∀ z ∈ K, ‖f z - p.eval z / q.eval z‖ < ε :=
  rational_approximation K hK U hU hKU f (hf.analyticOnNhd hU) ε hε

theorem prescribed_poles_approximation_of_holomorphic (K : Set ℂ) (hK : IsCompact K)
    (P : Set ℂ) (hP : MeetsBoundedComplementComponents K P)
    (U : Set ℂ) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z ∈ K, q.eval z ≠ 0) ∧
      (∀ a : ℂ, q.eval a = 0 → a ∈ P) ∧
      ∀ z ∈ K, ‖f z - p.eval z / q.eval z‖ < ε :=
  prescribed_poles_approximation K hK P hP U hU hKU f (hf.analyticOnNhd hU) ε hε

theorem polynomial_approximation_of_holomorphic (K : Set ℂ) (hK : IsCompact K)
    (hconn : IsConnected Kᶜ) (U : Set ℂ) (hU : IsOpen U)
    (hKU : K ⊆ U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖f z - p.eval z‖ < ε :=
  polynomial_approximation K hK hconn U hU hKU f (hf.analyticOnNhd hU) ε hε

end Runge
