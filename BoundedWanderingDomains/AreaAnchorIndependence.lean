/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.AnchoredCompactArea
import BoundedWanderingDomains.AreaGainSubadditivity

/-!
# Independence of the auxiliary omitted points

The two values used to construct a covering are not part of the intrinsic
metric. This is needed to insert auxiliary punctures into arbitrary domains.
-/

open Set MeasureTheory
open scoped ENNReal

namespace AreaDeficit

theorem closedComplementDensity_anchor_independent
    (A : Set ℂ) (hA : IsClosed A)
    {a b c d : ℂ} (hab : a ≠ b) (hcd : c ≠ d)
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A) (z : ℂ) :
    closedComplementDensity A hA hab ha hb z =
      closedComplementDensity A hA hcd hc hd z := by
  by_cases hz : z ∈ A
  · simp [closedComplementDensity, hz]
  · obtain ⟨p, hp⟩ :=
      RiemannDynamics.exists_disc_covering_complement_component hA hz hab ha hb
    rw [closedComplementDensity_eq_cover A hA hab ha hb hz hp,
      closedComplementDensity_eq_cover A hA hcd hc hd hz hp]

theorem closedComplementAreaWeight_anchor_independent
    (A : Set ℂ) (hA : IsClosed A)
    {a b c d : ℂ} (hab : a ≠ b) (hcd : c ≠ d)
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A) (z : ℂ) :
    closedComplementAreaWeight A hA hab ha hb z =
      closedComplementAreaWeight A hA hcd hc hd z := by
  simp only [closedComplementAreaWeight,
    closedComplementDensity_anchor_independent A hA hab hcd ha hb hc hd z]

/-- The curvature −1 hyperbolic area density is intrinsic to the domain. -/
theorem closedComplementHyperbolicAreaWeight_anchor_independent
    (A : Set ℂ) (hA : IsClosed A)
    {a b c d : ℂ} (hab : a ≠ b) (hcd : c ≠ d)
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A) (z : ℂ) :
    ENNReal.ofReal ((closedComplementDensity A hA hab ha hb z)^2) =
      ENNReal.ofReal ((closedComplementDensity A hA hcd hc hd z)^2) := by
  rw [closedComplementDensity_anchor_independent A hA hab hcd ha hb hc hd z]

/-- Monotonicity of curvature −1 area density, even if the two covering
constructions use different omitted-point anchors. -/
theorem hyperbolicAreaWeight_mono_any (A B : Set ℂ)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : A ⊆ B)
    {a b c d z : ℂ} (hab : a ≠ b) (hcd : c ≠ d)
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ B) (hd : d ∈ B)
    (hz : z ∉ B) :
    ENNReal.ofReal ((closedComplementDensity A hA hab ha hb z)^2) ≤
      ENNReal.ofReal ((closedComplementDensity B hB hcd hc hd z)^2) := by
  apply ENNReal.ofReal_le_ofReal
  have hp := le_of_lt (closedComplementDensity_pos A hA hab ha hb
    (fun hx => hz (hAB hx)))
  have hm := closedComplementDensity_mono A B hA hB hAB hab ha hb hz
  rw [closedComplementDensity_anchor_independent B hB hab hcd
    (hAB ha) (hAB hb) hc hd z] at hm
  nlinarith

/-- Inserting finitely many auxiliary punctures leaves an integration
domain unchanged up to a volume-null set. -/
theorem restrict_complement_union_finite
    (W A : Set ℂ) (E : Finset ℂ) :
    volume.restrict (W ∩ (A ∪ (↑E : Set ℂ))ᶜ) =
      volume.restrict (W ∩ Aᶜ) := by
  apply Measure.restrict_congr_set
  have hne : ∀ᵐ z : ℂ ∂volume, z ∉ (↑E : Set ℂ) := by
    rw [ae_iff]
    convert E.measure_zero volume using 1
    congr 1
    ext z
    simp
  filter_upwards [hne] with z hz
  simp [hz]

end AreaDeficit

#print axioms AreaDeficit.closedComplementDensity_anchor_independent
#print axioms AreaDeficit.closedComplementAreaWeight_anchor_independent
#print axioms AreaDeficit.closedComplementHyperbolicAreaWeight_anchor_independent
#print axioms AreaDeficit.hyperbolicAreaWeight_mono_any
#print axioms AreaDeficit.restrict_complement_union_finite
