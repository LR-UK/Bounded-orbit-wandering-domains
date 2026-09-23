import EremenkosConjecture.PrescribedBoundaryConstruction
import EremenkosConjecture.PathComponentTheorem
import EremenkosConjecture.LakesOfWada
import EremenkosConjecture.Theorem71
import EremenkosConjecture.ContinuumCounterexample

/-!
# Main statements for mathematical review

Start here to read the advertised results without following the construction.
Every statement below is checked by Lean against the completed proof named on
the following line. MAIN_RESULTS.md explains the notation and hypotheses;
PROOF_MAP.md explains how the proofs fit together.

This is the proved statement gallery for the wider library. The root Challenge
and Solution modules provide a separate comparison surface for selected results.
-/

open Set Metric Function Filter ComplexDynamics

namespace EremenkosConjecture.MainTheorems

/-- Theorem 1.2: every nonempty full compact continuum is exactly a connected
component of the escaping set of a transcendental entire function. -/
theorem theorem_1_2 (X : Set ℂ) (hX : IsCompact X) (hconn : IsConnected X)
    (hfull : IsConnected Xᶜ) :
    ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧ ∃ z ∈ escapingSet f,
      connectedComponentIn (escapingSet f) z = X :=
  EremenkosConjecture.theorem1_2 X hX hconn hfull

/-- Eremenko's conjecture fails: there is a transcendental entire function
with an escaping point whose only connected escaping subset is its singleton. -/
theorem eremenko_conjecture_false : ∃ (f : ℂ → ℂ) (z : ℂ),
    IsTranscendentalEntire f ∧ z ∈ escapingSet f ∧
      ∀ A : Set ℂ, IsConnected A → A ⊆ escapingSet f → z ∈ A → A = {z} :=
  EremenkosConjecture.eremenko_conjecture_false

/-- Theorem 7.1: the nonnegative real ray is Julia, its endpoint escapes,
the positive ray is bungee, and the indicated connected components are exact. -/
theorem theorem_7_1 : ∃ f : ℂ → ℂ,
    IsTranscendentalEntire f ∧ horizontalRay 0 ⊆ juliaSet f ∧ (0 : ℂ) ∈ escapingSet f ∧
    horizontalRay 0 \ {0} ⊆ bungeeSet f ∧
    connectedComponentIn (juliaSet f ∪ escapingSet f ∪ bungeeSet f) 0 = horizontalRay 0 ∧
    connectedComponentIn (escapingSet f) 0 = {0} :=
  EremenkosConjecture.theorem7_1

/-- A counterexample to the original connected-component version of Eremenko's conjecture. -/
theorem eremenko_counterexample : ∃ (f : ℂ → ℂ) (z : ℂ),
    IsTranscendentalEntire f ∧ z ∈ escapingSet f ∧ connectedComponentIn (escapingSet f) z = {z} :=
  EremenkosConjecture.eremenko_counterexample

/-- Theorem 7.1, with the distinguished endpoint translated from zero to `7i/2`. -/
theorem theorem_7_1_translated : ∃ f : ℂ → ℂ,
    IsTranscendentalEntire f ∧ horizontalRay rayBase ⊆ juliaSet f ∧ rayBase ∈ escapingSet f ∧
    horizontalRay rayBase \ {rayBase} ⊆ bungeeSet f ∧
    connectedComponentIn (juliaSet f ∪ escapingSet f ∪ bungeeSet f) rayBase = horizontalRay rayBase ∧
    connectedComponentIn (escapingSet f) rayBase = {rayBase} :=
  EremenkosConjecture.theorem7_1_translated

/-- Theorem 3.1: every full compact set is a uniformly escaping wandering compactum. -/
theorem theorem_3_1 (K : Set ℂ) (hK : IsCompact K) (hfull : IsConnected Kᶜ) :
    ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧
      (∀ n m : ℕ, n ≠ m → Disjoint ((f^[n]) '' K) ((f^[m]) '' K)) ∧
      EscapesUniformlyOn f K ∧ frontier K ⊆ juliaSet f ∧
      ∀ z ∈ interior K, IsWanderingDomain f (connectedComponentIn (interior K) z) :=
  EremenkosConjecture.wandering_compactum K hK hfull

/-- Proposition 3.2: prescribed compact nonseparating boundary sets; see UniformEscapeData for the explicit geometric hypotheses. -/
theorem proposition_3_2 (D : UniformEscapeData) :
    ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧
      MapsTo f (controlDisc 0) trappingDisc ∧
      (∀ n, MapsTo (f^[n + 1]) (D.P n) trappingDisc) ∧
      ∀ n, InjOn (f^[n]) (D.K n) ∧ MapsTo (f^[n]) (D.K n) (targetDisc n) :=
  EremenkosConjecture.UniformEscapeData.prescribed_boundary_itinerary D

/-- Proposition 3.3: add fast escape, with bounds at every nonnegative starting radius. -/
theorem proposition_3_3 (K : Set ℂ) (hK : IsCompact K)
    (hfull : IsConnected Kᶜ) :
    ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧
      (∀ n m : ℕ, n ≠ m → Disjoint ((f^[n]) '' K) ((f^[m]) '' K)) ∧
      EscapesUniformlyOn f K ∧ frontier K ⊆ juliaSet f ∧
      (∀ z ∈ interior K, IsWanderingDomain f (connectedComponentIn (interior K) z)) ∧
      K ⊆ fastEscapingSet f ∧
      ∀ r : ℝ, 0 ≤ r → K ⊆ fastEscapingSetAtRadius f r :=
  EremenkosConjecture.fast_escaping_wandering_compactum K hK hfull

/-- Theorem 3.4 and Remark 3.5: prescribed escaping and Julia path components, including singleton continua. -/
theorem theorem_3_4 (K : Set ℂ) (hK : IsCompact K)
    (hconn : IsConnected K) (hfull : IsConnected Kᶜ) :
    ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧ K ⊆ fastEscapingSet f ∧
      (∀ x ∈ K, pathComponentIn (escapingSet f) x = pathComponentIn K x) ∧
      (∀ x ∈ frontier K, pathComponentIn (juliaSet f) x = pathComponentIn (frontier K) x) :=
  EremenkosConjecture.fast_escaping_path_components K hK hconn hfull

/-- Counterexamples to the strong (curve-to-infinity) version, not the original connected-component conjecture. -/
theorem no_escaping_curve_to_infinity (K : Set ℂ) (hK : IsCompact K)
    (hconn : IsConnected K) (hfull : IsConnected Kᶜ) :
    ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧ K ⊆ fastEscapingSet f ∧
      (∀ x ∈ K, pathComponentIn (escapingSet f) x = pathComponentIn K x) ∧
      (∀ x ∈ frontier K, pathComponentIn (juliaSet f) x = pathComponentIn (frontier K) x) ∧
      (∀ γ : ℝ → ℂ, ContinuousOn γ (Ici 0) → γ 0 ∈ K → MapsTo γ (Ici 0) (escapingSet f) →
        ¬ Tendsto (fun t => ‖γ t‖) atTop atTop) :=
  EremenkosConjecture.strong_eremenko_counterexamples K hK hconn hfull

/-- Unconditional topological existence of countably many Lakes of Wada. -/
theorem topological_lakes_of_wada :
    ∃ X : Set ℂ, ∃ U : ℕ → Set ℂ, IsCompact X ∧ IsConnected X ∧ Injective U ∧
      Pairwise (Disjoint on U) ∧
      ∀ i, IsOpen (U i) ∧ IsConnected (U i) ∧ Bornology.IsBounded (U i) ∧ frontier (U i) = X :=
  EremenkosConjecture.exists_countably_many_lakes_of_wada

/-- Theorem 1.4, proved in Section 3: infinitely many wandering Fatou domains with the same boundary. -/
theorem theorem_1_4 :
    ∃ f : ℂ → ℂ, ∃ X : Set ℂ, ∃ U : ℕ → Set ℂ,
      IsTranscendentalEntire f ∧ IsCompact X ∧ IsConnected X ∧ X ⊆ juliaSet f ∧
      Injective U ∧ Pairwise (Disjoint on U) ∧
      ∀ i, IsWanderingDomain f (U i) ∧ frontier (U i) = X ∧
        closure (U i) ⊆ fastEscapingSet f ∧ EscapesUniformlyOn f (closure (U i)) :=
  EremenkosConjecture.wandering_lakes_of_wada

end EremenkosConjecture.MainTheorems
