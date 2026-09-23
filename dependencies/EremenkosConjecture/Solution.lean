import EremenkosConjecture.MainTheorems

/-! # Proved counterparts to Challenge.lean
This module imports completed proofs only. It does not import Challenge.
The four declaration types are reproduced verbatim from the statement surface.
The local Lean checks are distinct from a future Comparator/NanoDa run.
-/

open Set Metric Function Filter ComplexDynamics
namespace EremenkosConjecture.Palomar

/-- Eremenko's conjecture fails: there is a transcendental entire function
with an escaping point whose only connected escaping subset is its singleton. -/
theorem eremenko_conjecture_false : ∃ (f : ℂ → ℂ) (z : ℂ),
    IsTranscendentalEntire f ∧ z ∈ escapingSet f ∧
      ∀ A : Set ℂ, IsConnected A → A ⊆ escapingSet f → z ∈ A → A = {z} :=
  EremenkosConjecture.eremenko_conjecture_false

/-- Theorem 1.2: every nonempty full compact continuum is exactly a connected
component of the escaping set of a transcendental entire function. -/
theorem theorem_1_2 (X : Set ℂ) (hX : IsCompact X) (hconn : IsConnected X)
    (hfull : IsConnected Xᶜ) :
    ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧ ∃ z ∈ escapingSet f,
      connectedComponentIn (escapingSet f) z = X :=
  EremenkosConjecture.theorem1_2 X hX hconn hfull

/-- Theorem 7.1: the nonnegative real ray is Julia, its endpoint escapes,
the positive ray is bungee, and the indicated connected components are exact. -/
theorem theorem_7_1 : ∃ f : ℂ → ℂ,
    IsTranscendentalEntire f ∧ horizontalRay 0 ⊆ juliaSet f ∧ (0 : ℂ) ∈ escapingSet f ∧
    horizontalRay 0 \ {0} ⊆ bungeeSet f ∧
    connectedComponentIn (juliaSet f ∪ escapingSet f ∪ bungeeSet f) 0 = horizontalRay 0 ∧
    connectedComponentIn (escapingSet f) 0 = {0} :=
  EremenkosConjecture.theorem7_1

/-- Counterexamples to the strong (curve-to-infinity) version, not the original connected-component conjecture. -/
theorem no_escaping_curve_to_infinity (K : Set ℂ) (hK : IsCompact K)
    (hconn : IsConnected K) (hfull : IsConnected Kᶜ) :
    ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧ K ⊆ fastEscapingSet f ∧
      (∀ x ∈ K, pathComponentIn (escapingSet f) x = pathComponentIn K x) ∧
      (∀ x ∈ frontier K, pathComponentIn (juliaSet f) x = pathComponentIn (frontier K) x) ∧
      (∀ γ : ℝ → ℂ, ContinuousOn γ (Ici 0) → γ 0 ∈ K → MapsTo γ (Ici 0) (escapingSet f) →
        ¬ Tendsto (fun t => ‖γ t‖) atTop atTop) :=
  EremenkosConjecture.strong_eremenko_counterexamples K hK hconn hfull

end EremenkosConjecture.Palomar
