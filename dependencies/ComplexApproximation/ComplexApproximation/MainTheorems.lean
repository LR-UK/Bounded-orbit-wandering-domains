import Runge.LocalDomain
import ComplexApproximation.Topology.Nonseparation
import ComplexApproximation.ArakelianLocalDomain

/-!
# Main statements for mathematical review

Start here to read the advertised results without following the construction.
Every statement below is checked by Lean against the completed proof named on
the following line. MAIN_RESULTS.md explains the notation and hypotheses;
PROOF_MAP.md explains how the proofs fit together.

This is a proved statement gallery, not a Palomar Challenge/Comparator package.
-/

open Set Polynomial Runge
open scoped ContDiff

namespace ComplexApproximation.MainTheorems

/-- Runge: rational approximation on an arbitrary compact set. -/
theorem rational_runge (K : Set ℂ) (hK : IsCompact K)
    (f : K → ℂ) (hf : HasHolomorphicExtension K f) (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : ℂ[X], (∀ z ∈ K, q.eval z ≠ 0) ∧
      ∀ z : K, ‖f z - p.eval (z : ℂ) / q.eval (z : ℂ)‖ < ε :=
  Runge.rational_approximation_on_compact K hK f hf ε hε

/-- Runge: approximation with poles in the prescribed set. -/
theorem prescribed_poles_runge (K : Set ℂ) (hK : IsCompact K)
    (P : Set ℂ) (hP : MeetsBoundedComplementComponents K P)
    (f : K → ℂ) (hf : HasHolomorphicExtension K f) (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z ∈ K, q.eval z ≠ 0) ∧
      (∀ a : ℂ, q.eval a = 0 → a ∈ P) ∧
      ∀ z : K, ‖f z - p.eval (z : ℂ) / q.eval (z : ℂ)‖ < ε :=
  Runge.prescribed_poles_approximation_on_compact K hK P hP f hf ε hε

/-- Runge: polynomial approximation on a full compact set. -/
theorem polynomial_runge (K : Set ℂ) (hK : IsCompact K)
    (hconn : IsConnected Kᶜ) (f : K → ℂ) (hf : HasHolomorphicExtension K f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ z : K, ‖f z - p.eval (z : ℂ)‖ < ε :=
  Runge.polynomial_approximation_on_compact K hK hconn f hf ε hε

/-- The open-domain interface: the function has domain U, not the whole plane. -/
theorem polynomial_runge_on_domain (K : Set ℂ) (hK : IsCompact K)
    (hconn : IsConnected Kᶜ) (U : Set ℂ) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : U → ℂ) (hf : IsHolomorphicFunctionOn U f) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ (z : ℂ) (hz : z ∈ K), ‖f ⟨z, hKU hz⟩ - p.eval z‖ < ε :=
  Runge.polynomial_approximation_on_domain K hK hconn U hU hKU f hf ε hε

/-- A domain homeomorphism preserves fullness. A conformal isomorphism is
a special case; simple connectivity and ambient extensions are unnecessary. -/
theorem fullness_under_domain_homeomorphism
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hUc : IsConnected U) (hVc : IsConnected V) (e : U ≃ₜ V)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) (hfull : IsConnected Kᶜ) :
    IsConnected ((fun z : U => (e z : ℂ)) '' ((↑) ⁻¹' K))ᶜ :=
  ComplexApproximation.isConnected_compl_image_domain_homeomorph hU hV hUc hVc e K hK hKU hfull

/-- Arakelian: a neighbourhood-holomorphic function on a closed set satisfying
the explicit no-holes and bounded-exhaustion-holes conditions is uniformly
approximable by an entire function. The input function has domain `E`. -/
theorem arakelian (E : Set ℂ) (hE : ComplexApproximation.IsArakelian E)
    (f : E → ℂ) (hf : HasHolomorphicExtension E f) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z : E, ‖g z - f z‖ < ε :=
  ComplexApproximation.arakelian_approximation_on_closed E hE f hf ε hε

/-- Cauchy–Pompeiu for a smooth compactly supported complex-valued function.
The normalized solver divides the Cauchy transform by `2πi`, and the defect
is `2i` times the usual antiholomorphic derivative. -/
theorem cauchy_pompeiu_compact (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) :
    ComplexApproximation.solveCauchyRiemann (Runge.cauchyRiemannDefect g) = g :=
  ComplexApproximation.cauchyPompeiu_compact g hg hc

end ComplexApproximation.MainTheorems
