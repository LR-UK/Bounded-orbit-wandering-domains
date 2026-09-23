import Runge.Interpolation
import FunctionTheory.Analytic.JetLocalDegree

open Set Filter Polynomial FunctionTheory
open scoped Topology

namespace Runge

set_option autoImplicit false

/-- Polynomial Runge approximation with the prescribed values and local
degrees at finitely many locally nonconstant holomorphic germs. -/
theorem polynomial_approximation_preserving_marked_local_degrees
    (K : Set ℂ) (hK : IsCompact K) (hfull : IsConnected Kᶜ)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f K)
    (s : Finset ℂ) (hsK : ∀ a ∈ s, a ∈ K)
    (hsnc : ∀ a ∈ s, ¬ ∀ᶠ z in 𝓝 a, f z = f a)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℂ[X],
      (∀ a ∈ K, ‖f a - p.eval a‖ < ε) ∧
      ∀ a ∈ s, p.eval a = f a ∧
        analyticOrderAt (fun z => p.eval z - p.eval a) a =
          analyticOrderAt (fun z => f z - f a) a := by
  classical
  have Horders : ∀ a : ℂ, ∃ m : ℕ, 0 < m ∧ (a ∈ s →
      ∀ g : ℂ → ℂ, AnalyticAt ℂ g a →
        (∀ k < m, iteratedDeriv k f a = iteratedDeriv k g a) →
        g a = f a ∧ analyticOrderAt (fun z => g z - g a) a =
          analyticOrderAt (fun z => f z - f a) a) := by
    intro a
    by_cases ha : a ∈ s
    · obtain ⟨m, hm, Hm⟩ := exists_jet_order_preserving_value_and_local_degree
        (hf a (hsK a ha)) (hsnc a ha)
      exact ⟨m, hm, fun _ => Hm⟩
    · exact ⟨1, by omega, fun H => (ha H).elim⟩
  choose m hm Hm using Horders
  let U := {z | AnalyticAt ℂ f z}
  have hKU : K ⊆ U := fun z hz => hf z hz
  have hU : IsOpen U := isOpen_analyticAt ℂ f
  have hfd : DifferentiableOn ℂ f U := fun z hz => hz.differentiableAt.differentiableWithinAt
  obtain ⟨p, hp, hjets⟩ := polynomial_approximation_with_interpolation
    K hK hfull U hU hKU f hfd s hsK m ε hε
  exact ⟨p, hp, fun a ha => Hm a ha p.eval
    (AnalyticOnNhd.eval_polynomial p a (mem_univ a)) (hjets a ha)⟩

end Runge
