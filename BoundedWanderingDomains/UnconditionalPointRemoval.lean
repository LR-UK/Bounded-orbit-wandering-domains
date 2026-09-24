/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.GeneralClosedPuncture
import BoundedWanderingDomains.CoveringTotalArea
import RiemannDynamics.Uniformization.PuncturedPlaneCovering

/-!
# Unconditional point-removal estimate on hyperbolic plane domains

Uniformisation and the finite-puncture total-area theorem supply all metric
properties required by the exhaustion argument.
-/

open Set MeasureTheory
open scoped ENNReal

namespace AreaDeficit

/-- The finite-puncture metric input is constructed from the already proved
holomorphic disc coverings and their exact total areas. -/
noncomputable def canonicalFinitePunctureMetricInput : FinitePunctureMetricInput := by
  classical
  have hex : ∀ P : Finset ℂ, ∃ p : ℂ → ℂ, 2 ≤ P.card →
      IsHolomorphicDiscCovering p ((↑P : Set ℂ)ᶜ) := by
    intro P
    by_cases hP : 2 ≤ P.card
    · obtain ⟨p, hp⟩ :=
        RiemannDynamics.exists_disc_covering_finitely_punctured_plane P hP
      exact ⟨p, fun _ => hp⟩
    · exact ⟨fun _ => 0, fun hP' => (hP hP').elim⟩
  choose p hp using hex
  refine ⟨fun P => coveringDensity (p P), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hP z hz
    exact (hp P hP).density_pos hz
  · intro P hP
    exact fun z hz => ((hp P hP).density_contDiffAt hz).contDiffWithinAt
  · intro P hP z hz
    exact (hp P hP).density_curvature hz
  · intro P hP g hg hgP
    exact (hp P hP).density_schwarz hg hgP
  · intro P hP z hz
    exact (hp P hP).density_extremal hz
  · intro P hP
    exact (hp P hP).total_area hP

/-- Removing finitely many additional points has normalised area cost at
most their number, even when the original domain has infinite area. -/
theorem finite_removal_gain_le_card
    (A : Set ℂ) (hA : IsClosed A) (E : Finset ℂ)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A) :
    (∫⁻ z in (A ∪ (↑E : Set ℂ))ᶜ,
      closedComplementAreaWeight (A ∪ (↑E : Set ℂ))
        (hA.union E.finite_toSet.isClosed) hab
        (Or.inl ha) (Or.inl hb) z -
      closedComplementAreaWeight A hA hab ha hb z) ≤ (E.card : ℝ≥0∞) := by
  obtain ⟨P, hP, hPa, hPb, hrep⟩ := exists_finite_exhaustion_closed A hA ha hb
  have hrep' : A ∪ (↑E : Set ℂ) =
      closure (⋃ n, (↑(P n ∪ E) : Set ℂ)) := by
    have hsets : (⋃ n, (↑(P n ∪ E) : Set ℂ)) =
        (⋃ n, (↑(P n) : Set ℂ)) ∪ (↑E : Set ℂ) := by
      ext z
      simp only [mem_iUnion, Finset.mem_coe, Finset.mem_union, mem_union]
      constructor
      · rintro ⟨n, hn | hn⟩
        · exact Or.inl ⟨n, hn⟩
        · exact Or.inr hn
      · rintro (⟨n, hn⟩ | hn)
        · exact ⟨n, Or.inl hn⟩
        · exact ⟨0, Or.inr hn⟩
    rw [hsets, closure_union, ← hrep, E.finite_toSet.isClosed.closure_eq]
  exact canonicalFinitePunctureMetricInput.puncture_gain_bound_closed_exhaustion
    hP hab hPa hPb E A (A ∪ (↑E : Set ℂ)) hA
    (hA.union E.finite_toSet.isClosed) (subset_union_left)
    hrep hrep' ha hb (Or.inl ha) (Or.inl hb)

/-- Removing a point from a hyperbolic plane domain increases the curvature
−1 area of the new domain by at most `2π` (the integrand is normalised by
`2π`). The obstacle is closed and contains two distinct points, so each
component of its complement is hyperbolic. -/
theorem point_removal_gain_le_two_pi_normalised
    (A : Set ℂ) (hA : IsClosed A)
    {a b w : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A) :
    (∫⁻ z in (A ∪ {w})ᶜ,
      closedComplementAreaWeight (A ∪ {w}) (hA.union isClosed_singleton) hab
        (Or.inl ha) (Or.inl hb) z -
      closedComplementAreaWeight A hA hab ha hb z) ≤ (1 : ℝ≥0∞) :=
  canonicalFinitePunctureMetricInput.point_removal_gain_le_one A hA hab ha hb

end AreaDeficit

#print axioms AreaDeficit.canonicalFinitePunctureMetricInput
#print axioms AreaDeficit.finite_removal_gain_le_card
#print axioms AreaDeficit.point_removal_gain_le_two_pi_normalised
