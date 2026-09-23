import Runge.LocalDomain

namespace EremenkosConjecture

/-- Theorem 2.1 of the paper, with the function defined only on the compact set. -/
theorem polynomial_approximation (K : Set ℂ) (hK : IsCompact K)
    (hfull : IsConnected Kᶜ) (g : K → ℂ) (hg : Runge.HasHolomorphicExtension K g)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ z : K, ‖g z - p.eval (z : ℂ)‖ < ε :=
  Runge.polynomial_approximation_on_compact K hK hfull g hg ε hε

end EremenkosConjecture
