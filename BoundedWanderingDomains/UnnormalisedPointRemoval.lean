/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.UnconditionalPointRemoval
import BoundedWanderingDomains.AnchoredCompactArea

/-!
# Puncture cost in the curvature minus one hyperbolic metric

The earlier finite-puncture theorem was proved with an integral divided by
`2π`. We convert its conclusion once here. All subsequent theorem statements
use the genuine hyperbolic area form, whose density is the square of the
curvature −1 hyperbolic density.
-/

open Set MeasureTheory
open scoped ENNReal

namespace AreaDeficit

/-- Density of the area form for the unique complete metric of curvature −1. -/
noncomputable def hyperbolicAreaWeight (A : Set ℂ) (hA : IsClosed A)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((closedComplementDensity A hA hab ha hb z)^2)

private theorem ofReal_sq_eq_scaled (x : ℝ) :
    ENNReal.ofReal (x ^ 2) =
      ENNReal.ofReal (x ^ 2 / (2 * Real.pi)) * ENNReal.ofReal (2 * Real.pi) := by
  rw [← ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) Real.two_pi_pos.le)]
  congr 1
  exact (div_mul_cancel₀ _ (ne_of_gt Real.two_pi_pos)).symm

theorem hyperbolicAreaWeight_eq_normalised_mul (A : Set ℂ) (hA : IsClosed A)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A) (z : ℂ) :
    hyperbolicAreaWeight A hA hab ha hb z =
      closedComplementAreaWeight A hA hab ha hb z * ENNReal.ofReal (2 * Real.pi) := by
  unfold hyperbolicAreaWeight closedComplementAreaWeight
  exact ofReal_sq_eq_scaled _

/-- A single puncture increases the curvature −1 hyperbolic area by at
most `2π`, even when the original domain has infinite total area. -/
theorem point_removal_gain_le_two_pi
    (A : Set ℂ) (hA : IsClosed A)
    {a b w : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A) :
    (∫⁻ z in (A ∪ {w})ᶜ,
      hyperbolicAreaWeight (A ∪ {w}) (hA.union isClosed_singleton) hab
        (Or.inl ha) (Or.inl hb) z -
      hyperbolicAreaWeight A hA hab ha hb z) ≤ ENNReal.ofReal (2 * Real.pi) := by
  let c : ℝ≥0∞ := ENNReal.ofReal (2 * Real.pi)
  have hc : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmeas : Measurable (fun z =>
      closedComplementAreaWeight (A ∪ {w}) (hA.union isClosed_singleton)
        hab (Or.inl ha) (Or.inl hb) z -
      closedComplementAreaWeight A hA hab ha hb z) :=
    (measurable_closedComplementAreaWeight (A ∪ {w})
      (hA.union isClosed_singleton) hab (Or.inl ha) (Or.inl hb)).sub
      (measurable_closedComplementAreaWeight A hA hab ha hb)
  calc
    (∫⁻ z in (A ∪ {w})ᶜ,
      hyperbolicAreaWeight (A ∪ {w}) (hA.union isClosed_singleton)
        hab (Or.inl ha) (Or.inl hb) z -
      hyperbolicAreaWeight A hA hab ha hb z) =
      (∫⁻ z in (A ∪ {w})ᶜ,
        (closedComplementAreaWeight (A ∪ {w}) (hA.union isClosed_singleton)
          hab (Or.inl ha) (Or.inl hb) z -
        closedComplementAreaWeight A hA hab ha hb z) * c) := by
          congr 1
          funext z
          simp only [hyperbolicAreaWeight, closedComplementAreaWeight,
            ofReal_sq_eq_scaled]
          exact (ENNReal.sub_mul (fun _ _ => hc)).symm
    _ = (∫⁻ z in (A ∪ {w})ᶜ,
        closedComplementAreaWeight (A ∪ {w}) (hA.union isClosed_singleton)
          hab (Or.inl ha) (Or.inl hb) z -
        closedComplementAreaWeight A hA hab ha hb z) * c :=
          lintegral_mul_const c hmeas
    _ ≤ ENNReal.ofReal (2 * Real.pi) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right
          (point_removal_gain_le_two_pi_normalised A hA hab ha hb) (bot_le : (0 : ℝ≥0∞) ≤ c)

/-- Removing a finite set increases curvature −1 area by at most `2π`
per point, without a finite-total-area assumption. -/
theorem finite_removal_gain_le_two_pi_mul_card
    (A : Set ℂ) (hA : IsClosed A) (E : Finset ℂ)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A) :
    (∫⁻ z in (A ∪ (↑E : Set ℂ))ᶜ,
      hyperbolicAreaWeight (A ∪ (↑E : Set ℂ))
        (hA.union E.finite_toSet.isClosed) hab
        (Or.inl ha) (Or.inl hb) z -
      hyperbolicAreaWeight A hA hab ha hb z) ≤
      (E.card : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi) := by
  let c : ℝ≥0∞ := ENNReal.ofReal (2 * Real.pi)
  have hc : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmeas : Measurable (fun z =>
      closedComplementAreaWeight (A ∪ (↑E : Set ℂ))
        (hA.union E.finite_toSet.isClosed)
        hab (Or.inl ha) (Or.inl hb) z -
      closedComplementAreaWeight A hA hab ha hb z) :=
    (measurable_closedComplementAreaWeight (A ∪ (↑E : Set ℂ))
      (hA.union E.finite_toSet.isClosed) hab (Or.inl ha) (Or.inl hb)).sub
      (measurable_closedComplementAreaWeight A hA hab ha hb)
  calc
    (∫⁻ z in (A ∪ (↑E : Set ℂ))ᶜ,
      hyperbolicAreaWeight (A ∪ (↑E : Set ℂ))
        (hA.union E.finite_toSet.isClosed) hab (Or.inl ha) (Or.inl hb) z -
      hyperbolicAreaWeight A hA hab ha hb z) =
      (∫⁻ z in (A ∪ (↑E : Set ℂ))ᶜ,
        (closedComplementAreaWeight (A ∪ (↑E : Set ℂ))
            (hA.union E.finite_toSet.isClosed)
            hab (Or.inl ha) (Or.inl hb) z -
          closedComplementAreaWeight A hA hab ha hb z) * c) := by
          congr 1
          funext z
          simp only [hyperbolicAreaWeight, closedComplementAreaWeight,
            ofReal_sq_eq_scaled]
          exact (ENNReal.sub_mul (fun _ _ => hc)).symm
    _ = (∫⁻ z in (A ∪ (↑E : Set ℂ))ᶜ,
        closedComplementAreaWeight (A ∪ (↑E : Set ℂ))
          (hA.union E.finite_toSet.isClosed)
          hab (Or.inl ha) (Or.inl hb) z -
        closedComplementAreaWeight A hA hab ha hb z) * c :=
          lintegral_mul_const c hmeas
    _ ≤ (E.card : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right
        (finite_removal_gain_le_card A hA E hab ha hb) (bot_le : (0 : ℝ≥0∞) ≤ c)

end AreaDeficit
