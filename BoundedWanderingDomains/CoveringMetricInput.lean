import BoundedWanderingDomains.DiscCoveringMetric
import BoundedWanderingDomains.SubmissionDefinitions

open Set Metric MeasureTheory
open scoped ENNReal

namespace BoundedWanderingDomains

/-- Only two classical inputs remain: holomorphic universal coverings by the
disc, and the total-area formula for their induced curvature −1 metrics.

For each finite set P with at least two points, p restricts to a surjective
holomorphic covering from the unit disc onto ℂ ∖ P. Its induced density is
`2 / ((1 - ‖w‖²) * ‖p'(w)‖)`, where p(w) = z. The definition selects w;
`IsHolomorphicDiscCovering.fibre_density_eq` proves independence of that choice.
The normalised total area is |P| − 1, i.e. the area is 2π(|P| − 1).

Positivity, smoothness, curvature, Schwarz–Pick, and extremal discs are
conclusions proved from this input, not additional hypotheses. -/
def ClassicalDiscCoveringsAndArea : Prop :=
  ∀ P : Finset ℂ, 2 ≤ P.card → ∃ p : ℂ → ℂ,
    AreaDeficit.IsHolomorphicDiscCovering p ((↑P : Set ℂ)ᶜ) ∧
    (∫⁻ z : ℂ, ENNReal.ofReal ((AreaDeficit.coveringDensity p z)^2 / (2 * Real.pi))) =
      (P.card - 1 : ℕ)

/-- The full former density package follows from a disc covering and its area. -/
theorem classicalHyperbolicMetrics_of_coveringsAndArea
    (h : ClassicalDiscCoveringsAndArea) : ClassicalHyperbolicMetrics := by
  classical
  have hex : ∀ P : Finset ℂ, ∃ p : ℂ → ℂ, 2 ≤ P.card →
      AreaDeficit.IsHolomorphicDiscCovering p ((↑P : Set ℂ)ᶜ) ∧
      (∫⁻ z : ℂ, ENNReal.ofReal ((AreaDeficit.coveringDensity p z)^2 / (2 * Real.pi))) =
        (P.card - 1 : ℕ) := by
    intro P
    by_cases hP : 2 ≤ P.card
    · obtain ⟨p, hp⟩ := h P hP
      exact ⟨p, fun _ => hp⟩
    · exact ⟨fun _ => 0, fun hP' => (hP hP').elim⟩
  choose p hp using hex
  refine ⟨fun P => AreaDeficit.coveringDensity (p P), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hP z hz
    exact (hp P hP).1.density_pos hz
  · intro P hP z hz
    exact ((hp P hP).1.density_contDiffAt hz).contDiffWithinAt
  · intro P hP z hz
    exact (hp P hP).1.density_curvature hz
  · intro P hP g hg hgP
    exact (hp P hP).1.density_schwarz hg hgP
  · intro P hP z hz
    exact (hp P hP).1.density_extremal hz
  · intro P hP
    exact (hp P hP).2

end BoundedWanderingDomains
