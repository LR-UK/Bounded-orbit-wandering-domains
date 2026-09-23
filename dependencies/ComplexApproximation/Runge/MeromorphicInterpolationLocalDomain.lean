import Runge.MeromorphicInterpolation
import FunctionTheory.Meromorphic.LocalDomain

open Set Filter Polynomial
open scoped Topology

namespace Runge

set_option autoImplicit false

/-- Meromorphic interpolation for a function defined only on its open domain.
Regular-point derivatives use the germ of its internal extension, and the error
extends analytically across every pole in the compact approximation set. -/
theorem meromorphic_prescribed_poles_approximation_with_interpolation_on_domain
    (K : Set ℂ) (hK : IsCompact K)
    (P : Set ℂ) (hP : MeetsBoundedComplementComponents K P)
    (U : Set ℂ) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : U → ℂ) (hf : FunctionTheory.IsMeromorphicFunctionOn U f)
    (s : Finset ℂ) (hsK : ∀ a ∈ s, a ∈ K)
    (hsreg : ∀ a ∈ s, AnalyticAt ℂ (FunctionTheory.domainExtension f) a)
    (m : ℂ → ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (p q : ℂ[X]) (e : ℂ → ℂ), q ≠ 0 ∧
      (∀ a, q.eval a = 0 →
        (a ∈ K ∧ ¬ AnalyticAt ℂ (FunctionTheory.domainExtension f) a) ∨ a ∈ P) ∧
      (∀ a ∈ K, AnalyticAt ℂ (FunctionTheory.domainExtension f) a → q.eval a ≠ 0) ∧
      AnalyticOnNhd ℂ e K ∧
      (∀ a ∈ K, ‖e a‖ < ε) ∧
      (∀ (a : ℂ) (ha : a ∈ K), AnalyticAt ℂ (FunctionTheory.domainExtension f) a →
        ‖f ⟨a, hKU ha⟩ - p.eval a / q.eval a‖ < ε) ∧
      (∀ a ∈ K, (fun z => FunctionTheory.domainExtension f z - p.eval z / q.eval z)
        =ᶠ[𝓝[≠] a] e) ∧
      ∀ a ∈ s, ∀ k < m a,
        iteratedDeriv k (FunctionTheory.domainExtension f) a =
          iteratedDeriv k (fun z => p.eval z / q.eval z) a := by
  obtain ⟨p, q, e, hq, hpoles, hreg, he, hbound, hpoint, hgerm, hjets⟩ :=
    meromorphic_prescribed_poles_approximation_with_interpolation K hK P hP
      (FunctionTheory.domainExtension f) (fun z hz => hf.meromorphicOn_extension hU z (hKU hz))
      s hsK hsreg m ε hε
  refine ⟨p, q, e, hq, hpoles, hreg, he, hbound, ?_, hgerm, hjets⟩
  intro a ha hfa
  simpa only [FunctionTheory.domainExtension_apply f a (hKU ha)] using hpoint a ha hfa

end Runge
