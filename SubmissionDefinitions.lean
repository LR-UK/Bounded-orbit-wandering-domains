import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import ComplexDynamics.Basic

open Set Metric Function Filter MeasureTheory
open scoped Topology ENNReal

namespace BoundedWanderingDomains

/-- The classical curvature −1 hyperbolic metric facts for finitely
punctured planes. This is a proposition, not a global axiom. -/
def ClassicalHyperbolicMetrics : Prop :=
  ∃ ρ : Finset ℂ → ℂ → ℝ,
    (∀ P : Finset ℂ, 2 ≤ P.card → ∀ z, z ∉ P → 0 < ρ P z) ∧
    (∀ P : Finset ℂ, 2 ≤ P.card → ContDiffOn ℝ 2 (ρ P) ((↑P : Set ℂ)ᶜ)) ∧
    (∀ P : Finset ℂ, 2 ≤ P.card → ∀ z, z ∉ P →
      Laplacian.laplacian (fun w => Real.log (ρ P w)) z = (ρ P z)^2) ∧
    (∀ P : Finset ℂ, 2 ≤ P.card → ∀ p : ℂ → ℂ,
      DifferentiableOn ℂ p (ball 0 1) → MapsTo p (ball 0 1) ((↑P : Set ℂ)ᶜ) →
      ρ P (p 0) * ‖deriv p 0‖ ≤ 2) ∧
    (∀ P : Finset ℂ, 2 ≤ P.card → ∀ z, z ∉ P → ∃ p : ℂ → ℂ,
      DifferentiableOn ℂ p (ball 0 1) ∧ MapsTo p (ball 0 1) ((↑P : Set ℂ)ᶜ) ∧
      p 0 = z ∧ ρ P z * ‖deriv p 0‖ = 2) ∧
    (∀ P : Finset ℂ, 2 ≤ P.card →
      (∫⁻ z : ℂ, ENNReal.ofReal ((ρ P z)^2 / (2 * Real.pi))) = (P.card - 1 : ℕ))

/-- The interior of the set of points whose entire forward orbit stays
in V. The values of the total function outside V play no role. -/
def trappedInterior (f : ℂ → ℂ) (V : Set ℂ) : Set ℂ :=
  interior {z | ∀ n : ℕ, f^[n] z ∈ V}

/-- Eventually injective on each fixed intrinsic disc about the orbit
point. The radius parameter r is in (0,1) in a normalized Riemann chart;
the corresponding curvature −1 radius is 2 artanh r. N may depend on r. -/
def EventuallyInjectiveOnLargeDiscs (f : ℂ → ℂ) (U : ℕ → Set ℂ) (z : ℕ → ℂ) : Prop :=
  ∀ r : ℝ, 0 < r → r < 1 → ∃ N : ℕ, ∀ n ≥ N, ∃ u : ℂ → ℂ,
    DifferentiableOn ℂ u (U n) ∧ BijOn u (U n) (ball 0 1) ∧ u (z n) = 0 ∧
      InjOn f (U n ∩ u ⁻¹' ball 0 r)

end BoundedWanderingDomains
