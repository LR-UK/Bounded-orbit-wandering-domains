import Runge.Interpolation
import Runge.LocalDomain

/-!
# Finite interpolation for functions with their actual domain

Only values on the open domain `U` are part of the input. Derivatives at the
marked points are computed using the existing internal extension; since all
marked points lie in the open set, their germs are independent of values
outside `U`. Set `m a = M + 1` to prescribe orders zero through `M`.
-/

open Polynomial

namespace Runge

set_option autoImplicit false

theorem polynomial_approximation_with_interpolation_on_domain
    (K : Set ℂ) (hK : IsCompact K) (hconn : IsConnected Kᶜ)
    (U : Set ℂ) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : U → ℂ) (hf : IsHolomorphicFunctionOn U f)
    (s : Finset ℂ) (hsK : ∀ a ∈ s, a ∈ K) (m : ℂ → ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℂ[X],
      (∀ (z : ℂ) (hz : z ∈ K), ‖f ⟨z, hKU hz⟩ - p.eval z‖ < ε) ∧
      ∀ a ∈ s, ∀ k < m a,
        iteratedDeriv k (domainExtension f) a = iteratedDeriv k (fun z => p.eval z) a := by
  obtain ⟨p, herr, hjet⟩ := polynomial_approximation_with_interpolation K hK hconn
    U hU hKU (domainExtension f) (hf.differentiableOn_extension hU) s hsK m ε hε
  exact ⟨p, fun z hz => by simpa [domainExtension, hKU hz] using herr z hz, hjet⟩

theorem prescribed_poles_approximation_with_interpolation_on_domain
    (K : Set ℂ) (hK : IsCompact K)
    (P : Set ℂ) (hP : MeetsBoundedComplementComponents K P)
    (U : Set ℂ) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : U → ℂ) (hf : IsHolomorphicFunctionOn U f)
    (s : Finset ℂ) (hsK : ∀ a ∈ s, a ∈ K) (m : ℂ → ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z ∈ K, q.eval z ≠ 0) ∧
      (∀ a : ℂ, q.eval a = 0 → a ∈ P) ∧
      (∀ (z : ℂ) (hz : z ∈ K), ‖f ⟨z, hKU hz⟩ - p.eval z / q.eval z‖ < ε) ∧
      ∀ a ∈ s, ∀ k < m a,
        iteratedDeriv k (domainExtension f) a =
          iteratedDeriv k (fun z => p.eval z / q.eval z) a := by
  obtain ⟨p, q, hq0, hqK, hqP, herr, hjet⟩ :=
    prescribed_poles_approximation_with_interpolation K hK P hP U hU hKU
      (domainExtension f) (hf.differentiableOn_extension hU) s hsK m ε hε
  exact ⟨p, q, hq0, hqK, hqP,
    fun z hz => by simpa [domainExtension, hKU hz] using herr z hz, hjet⟩

theorem rational_approximation_with_interpolation_on_domain
    (K : Set ℂ) (hK : IsCompact K)
    (U : Set ℂ) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : U → ℂ) (hf : IsHolomorphicFunctionOn U f)
    (s : Finset ℂ) (hsK : ∀ a ∈ s, a ∈ K) (m : ℂ → ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z ∈ K, q.eval z ≠ 0) ∧
      (∀ (z : ℂ) (hz : z ∈ K), ‖f ⟨z, hKU hz⟩ - p.eval z / q.eval z‖ < ε) ∧
      ∀ a ∈ s, ∀ k < m a,
        iteratedDeriv k (domainExtension f) a =
          iteratedDeriv k (fun z => p.eval z / q.eval z) a := by
  obtain ⟨p, q, hq0, hqK, herr, hjet⟩ := rational_approximation_with_interpolation
    K hK U hU hKU (domainExtension f) (hf.differentiableOn_extension hU) s hsK m ε hε
  exact ⟨p, q, hq0, hqK,
    fun z hz => by simpa [domainExtension, hKU hz] using herr z hz, hjet⟩

end Runge
