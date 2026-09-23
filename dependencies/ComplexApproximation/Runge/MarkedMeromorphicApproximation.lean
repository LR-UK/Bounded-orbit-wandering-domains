import Runge.MeromorphicIncrement
import FunctionTheory.Analytic.JetLocalDegree

open Set Filter Polynomial FunctionTheory
open scoped Topology

namespace Runge

set_option autoImplicit false

/-- Meromorphic approximation preserving every prescribed marked value and
centred local degree. The input marks are regular locally nonconstant germs;
the finite interpolation orders are chosen within the proof. -/
theorem meromorphic_approximation_preserving_marked_local_degrees
    (K : Set ℂ) (hK : IsCompact K)
    (P : Set ℂ) (hP : MeetsBoundedComplementComponents K P)
    (f : ℂ → ℂ) (hf : MeromorphicOn f K)
    (s : Finset ℂ) (hsK : ∀ a ∈ s, a ∈ K)
    (hsreg : ∀ a ∈ s, AnalyticAt ℂ f a)
    (hsnc : ∀ a ∈ s, ¬ ∀ᶠ z in 𝓝 a, f z = f a)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (p q : ℂ[X]) (g : ℂ → ℂ), q ≠ 0 ∧
      (∀ a, q.eval a = 0 → (a ∈ K ∧ ¬ AnalyticAt ℂ f a) ∨ a ∈ P) ∧
      MeromorphicOn g univ ∧
      (∀ a, g =ᶠ[𝓝[≠] a] (fun z => p.eval z / q.eval z)) ∧
      AnalyticOnNhd ℂ (fun z => f z - g z) K ∧
      (∀ a ∈ K, ‖f a - g a‖ < ε) ∧
      (∀ a ∈ K, AnalyticAt ℂ f a → AnalyticAt ℂ g a) ∧
      ∀ a ∈ s, g a = f a ∧
        analyticOrderAt (fun z => g z - g a) a =
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
        (hsreg a ha) (hsnc a ha)
      exact ⟨m, hm, fun _ => Hm⟩
    · exact ⟨1, by omega, fun H => (ha H).elim⟩
  choose m hm Hm using Horders
  obtain ⟨p, q, g, hq, hpoles, _, hg, hgr, hdiff, hbound, hreg, hjets⟩ :=
    meromorphic_approximation_with_analytic_increment K hK P hP f hf s hsK hsreg m ε hε
  exact ⟨p, q, g, hq, hpoles, hg, hgr, hdiff, hbound, hreg,
    fun a ha => Hm a ha g (hreg a (hsK a ha) (hsreg a ha)) (hjets a ha)⟩

end Runge
