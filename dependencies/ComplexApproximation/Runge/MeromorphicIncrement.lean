import Runge.MeromorphicInterpolation
import FunctionTheory.Meromorphic.ApproximationRepresentative

open Set Filter Polynomial FunctionTheory
open scoped Topology

namespace Runge

set_option autoImplicit false

/-- Meromorphic Runge approximation with finite jets, choosing harmless
complex representative values at poles so that the error is analytic there
as well. The approximant is a rational meromorphic map in the sense of equal
punctured germs, and its new poles remain confined to the allowed set. -/
theorem meromorphic_approximation_with_analytic_increment
    (K : Set ℂ) (hK : IsCompact K)
    (P : Set ℂ) (hP : MeetsBoundedComplementComponents K P)
    (f : ℂ → ℂ) (hf : MeromorphicOn f K)
    (s : Finset ℂ) (hsK : ∀ a ∈ s, a ∈ K)
    (hsreg : ∀ a ∈ s, AnalyticAt ℂ f a) (m : ℂ → ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (p q : ℂ[X]) (g : ℂ → ℂ), q ≠ 0 ∧
      (∀ a, q.eval a = 0 → (a ∈ K ∧ ¬ AnalyticAt ℂ f a) ∨ a ∈ P) ∧
      (∀ a ∈ K, AnalyticAt ℂ f a → q.eval a ≠ 0) ∧
      MeromorphicOn g univ ∧
      (∀ a, g =ᶠ[𝓝[≠] a] (fun z => p.eval z / q.eval z)) ∧
      AnalyticOnNhd ℂ (fun z => f z - g z) K ∧
      (∀ a ∈ K, ‖f a - g a‖ < ε) ∧
      (∀ a ∈ K, AnalyticAt ℂ f a → AnalyticAt ℂ g a) ∧
      ∀ a ∈ s, ∀ k < m a, iteratedDeriv k f a = iteratedDeriv k g a := by
  obtain ⟨p, q, e, hq, hpoles, hreg, he, hebound, _, herr, hjets⟩ :=
    meromorphic_prescribed_poles_approximation_with_interpolation
      K hK P hP f hf s hsK hsreg m ε hε
  let r : ℂ → ℂ := fun z => p.eval z / q.eval z
  have hr : MeromorphicOn r univ := by
    intro a _
    exact ((AnalyticOnNhd.eval_polynomial p a (mem_univ a)).meromorphicAt).div
      ((AnalyticOnNhd.eval_polynomial q a (mem_univ a)).meromorphicAt)
  obtain ⟨g, hg, hlocal, hdiff, hgr, _, hgreg⟩ :=
    exists_meromorphic_approximation_representative hK.isClosed f r e hr he herr
  refine ⟨p, q, g, hq, hpoles, hreg, hg, hgr, hdiff, ?_, hgreg, ?_⟩
  · intro a ha
    rw [(hlocal a ha).eq_of_nhds]
    exact hebound a ha
  · intro a ha k hk
    have hga := hgreg a (hsK a ha) (hsreg a ha)
    have hra : AnalyticAt ℂ r a :=
      (AnalyticOnNhd.eval_polynomial p a (mem_univ a)).div
        (AnalyticOnNhd.eval_polynomial q a (mem_univ a)) (hreg a (hsK a ha) (hsreg a ha))
    have Heq := eventuallyEq_of_punctured_eq_of_continuousAt
      hga.continuousAt hra.continuousAt (hgr a)
    exact (hjets a ha k hk).trans (Heq.iteratedDeriv_eq k).symm

end Runge
