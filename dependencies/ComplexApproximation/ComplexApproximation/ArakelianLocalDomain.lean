import ComplexApproximation.Arakelian
import Runge.LocalDomain

/-! # Arakelian approximation for functions on their actual domain -/

open Set Runge

namespace ComplexApproximation

theorem arakelian_approximation_on_domain (E : Set ℂ) (hE : IsArakelian E)
    (U : Set ℂ) (hU : IsOpen U) (hEU : E ⊆ U)
    (f : U → ℂ) (hf : IsHolomorphicFunctionOn U f) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ (z : ℂ) (hz : z ∈ E), ‖g z - f ⟨z, hEU hz⟩‖ < ε := by
  obtain ⟨g, hg, herr⟩ := arakelian_approximation_of_holomorphic E hE U hU hEU
    (domainExtension f) (hf.differentiableOn_extension hU) ε hε
  exact ⟨g, hg, fun z hz => by simpa only [domainExtension_apply f z (hEU hz)] using herr z hz⟩

/-- A function given only on the closed set, with the explicit hypothesis
that it has a holomorphic extension to a neighbourhood. -/
theorem arakelian_approximation_on_closed (E : Set ℂ) (hE : IsArakelian E)
    (f : E → ℂ) (hf : HasHolomorphicExtension E f) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z : E, ‖g z - f z‖ < ε := by
  obtain ⟨U, hU, hEU, h, hh, heq⟩ := hf
  obtain ⟨g, hg, herr⟩ := arakelian_approximation_on_domain E hE U hU hEU h hh ε hε
  exact ⟨g, hg, fun z => by simpa only [heq z] using herr z z.property⟩

end ComplexApproximation
