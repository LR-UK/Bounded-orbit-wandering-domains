/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.SphereHyperbolicArea
import BoundedWanderingDomains.UnnormalisedPointRemoval
import BoundedWanderingDomains.SpherePointRemoval
import BoundedWanderingDomains.SphereAreaGainTransitivity

/-!
# Removing finitely many finite points from a sphere domain

In the chart with pole at infinity, the planar finite-puncture estimate gives
the corresponding curvature `-1` estimate for sphere domains.
-/

open Set Function OnePoint MeasureTheory
open scoped Topology RiemannSphere ENNReal

namespace AreaDeficit

/-- A finite set of complex points, regarded as a subset of the sphere. -/
def sphereFiniteSet (E : Finset ℂ) : Set (OnePoint ℂ) :=
  ((fun z : ℂ => ((z : ℂ) : OnePoint ℂ)) '' (↑E : Set ℂ))

private theorem pole_infty_preimage_sphereFiniteSet
    (A : Set (OnePoint ℂ)) (E : Finset ℂ) :
    (spherePoleChart (∞ : OnePoint ℂ)) ⁻¹' (A ∪ sphereFiniteSet E) =
      (spherePoleChart (∞ : OnePoint ℂ)) ⁻¹' A ∪ (↑E : Set ℂ) := by
  ext z
  constructor
  · rintro (hzA | ⟨w, hwE, hwz⟩)
    · exact Or.inl hzA
    · apply Or.inr
      have : w = z := OnePoint.coe_injective hwz
      simpa only [this] using hwE
  · rintro (hzA | hzE)
    · exact Or.inl hzA
    · exact Or.inr ⟨z, hzE, rfl⟩

/-- Removing `E` from a sphere domain costs at most `2π * #E`, when the
metric data use the standard finite chart.  This is the form needed for
finite puncture exhaustions of planar dynamics. -/
theorem sphere_finite_removal_gain_le_two_pi_mul_card
    {A : Set (OnePoint ℂ)} (hA : IsClosed A)
    (D : SphereHyperbolicMetricData A) (hpole : D.pole = (∞ : OnePoint ℂ))
    (E : Finset ℂ) :
    sphereHyperbolicAreaGain A hA (A ∪ sphereFiniteSet E)
      (hA.union (E.finite_toSet.image
        (fun z : ℂ => ((z : ℂ) : OnePoint ℂ))).isClosed)
      subset_union_left D Set.univ ≤
        (E.card : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi) := by
  have hone : D.anchorOne ∈
      (spherePoleChart (∞ : OnePoint ℂ)) ⁻¹' A := by
    simpa only [hpole] using D.anchorOne_mem
  have htwo : D.anchorTwo ∈
      (spherePoleChart (∞ : OnePoint ℂ)) ⁻¹' A := by
    simpa only [hpole] using D.anchorTwo_mem
  have hplane := finite_removal_gain_le_two_pi_mul_card
    ((spherePoleChart (∞ : OnePoint ℂ)) ⁻¹' A)
    (closed_sphere_set_in_pole_chart hA (∞ : OnePoint ℂ)) E D.anchor_ne hone htwo
  unfold sphereHyperbolicAreaGain
  simp only [univ_inter]
  simpa only [hpole, pole_infty_preimage_sphereFiniteSet,
    preimage_compl] using hplane

/-- The finite-puncture estimate on the sphere, including punctures at
infinity and without choosing a preferred pole. -/
theorem sphere_finite_puncture_gain_le_two_pi_mul_card
    (E : Finset (OnePoint ℂ))
    (A : Set (OnePoint ℂ)) (hA : IsClosed A)
    (D : SphereHyperbolicMetricData A) :
    sphereHyperbolicAreaGain A hA (A ∪ (↑E : Set (OnePoint ℂ)))
      (hA.union E.finite_toSet.isClosed) subset_union_left D Set.univ ≤
        (E.card : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi) := by
  classical
  induction E using Finset.induction_on with
  | empty => simp [sphereHyperbolicAreaGain]
  | @insert w E hw ih =>
    let B := A ∪ (↑E : Set (OnePoint ℂ))
    have hB : IsClosed B := hA.union E.finite_toSet.isClosed
    have heq : A ∪ (↑(insert w E) : Set (OnePoint ℂ)) = B ∪ {w} := by
      ext x
      simp only [B, Finset.coe_insert, mem_union, mem_insert_iff, mem_singleton_iff]
      tauto
    have hpoint : sphereHyperbolicAreaGain B hB (B ∪ {w})
        (hB.union isClosed_singleton) subset_union_left
        (D.mono subset_union_left) Set.univ ≤ ENNReal.ofReal (2 * Real.pi) := by
      by_cases hwB : w ∈ B
      · have hu : B ∪ {w} = B := union_eq_self_of_subset_right (singleton_subset_iff.mpr hwB)
        simp [hu, sphereHyperbolicAreaGain]
      · exact sphere_point_removal_gain_le_two_pi hB (D.mono subset_union_left) hwB
    have ht := sphereHyperbolicAreaGain_trans (C := B ∪ {w}) hA hB (hB.union isClosed_singleton)
      subset_union_left subset_union_left D (W := Set.univ)
    simp only [heq]
    calc
      _ ≤ sphereHyperbolicAreaGain A hA B hB subset_union_left D Set.univ +
          sphereHyperbolicAreaGain B hB (B ∪ {w}) (hB.union isClosed_singleton)
            subset_union_left (D.mono subset_union_left) Set.univ := ht
      _ ≤ (E.card : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi) +
          ENNReal.ofReal (2 * Real.pi) := add_le_add ih hpoint
      _ = _ := by rw [Finset.card_insert_of_notMem hw]; simp [add_mul]

end AreaDeficit
