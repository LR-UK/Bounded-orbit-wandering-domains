/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.SphereCompactRemoval
import BoundedWanderingDomains.SphereFiniteRemoval
import BoundedWanderingDomains.SphereAreaGainTransitivity

/-!
# Compact removal together with finitely many punctures

The compact-removal bound and the `2π` cost per finite point combine into a
single bound, uniform over the original hyperbolic sphere domain.
-/

open Set Function OnePoint MeasureTheory
open scoped Topology RiemannSphere ENNReal

namespace AreaDeficit

/-- Uniform compact-removal gain followed by a fixed finite set of planar
punctures.  The standard pole at infinity is the form used by the dynamical
finite-puncture exhaustion. -/
theorem uniform_compact_finite_gain_sphere
    {K L : Set (OnePoint ℂ)} (hK : IsCompact K) (hL : IsCompact L)
    (hKL : Disjoint K L) (E : Finset ℂ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (A : Set (OnePoint ℂ)) (hA : IsClosed A)
        (D : SphereHyperbolicMetricData A)
        (_hpole : D.pole = (∞ : OnePoint ℂ)),
        sphereHyperbolicAreaGain A hA
          ((A ∪ K) ∪ sphereFiniteSet E)
          ((hA.union hK.isClosed).union
            (E.finite_toSet.image
              (fun z : ℂ => ((z : ℂ) : OnePoint ℂ))).isClosed)
          (subset_union_left.trans subset_union_left) D L ≤ C := by
  obtain ⟨M, hMtop, hM⟩ := uniform_compact_gain_sphere hK hL hKL
  let cost : ℝ≥0∞ := (E.card : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi)
  refine ⟨M + cost, ENNReal.add_ne_top.mpr
    ⟨hMtop, ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top⟩, ?_⟩
  intro A hA D hpole
  let B : Set (OnePoint ℂ) := A ∪ K
  let C : Set (OnePoint ℂ) := B ∪ sphereFiniteSet E
  have hB : IsClosed B := hA.union hK.isClosed
  have hE : IsClosed (sphereFiniteSet E) :=
    (E.finite_toSet.image
      (fun z : ℂ => ((z : ℂ) : OnePoint ℂ))).isClosed
  have hC : IsClosed C := hB.union hE
  let DB : SphereHyperbolicMetricData B := D.mono subset_union_left
  have hDBpole : DB.pole = (∞ : OnePoint ℂ) := hpole
  have hcompact := hM A hA D
  have hfiniteUniv := sphere_finite_removal_gain_le_two_pi_mul_card
    hB DB hDBpole E
  have hfiniteL : sphereHyperbolicAreaGain B hB C hC subset_union_left DB L ≤ cost := by
    apply hfiniteUniv.trans'
    unfold sphereHyperbolicAreaGain
    apply lintegral_mono_set
    intro z hz
    exact ⟨Set.mem_univ _, hz.2⟩
  have htrans := sphereHyperbolicAreaGain_trans hA hB hC
    subset_union_left subset_union_left D (W := L)
  change sphereHyperbolicAreaGain A hA C hC
      (subset_union_left.trans subset_union_left) D L ≤ M + cost
  exact htrans.trans (add_le_add hcompact hfiniteL)

/-- Uniform version for a moving finite set containing at most `q` points. -/
theorem uniform_compact_finite_gain_sphere_le
    (q : ℕ) {K L : Set (OnePoint ℂ)} (hK : IsCompact K) (hL : IsCompact L)
    (hKL : Disjoint K L) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (E : Finset ℂ) (A : Set (OnePoint ℂ)) (hA : IsClosed A)
        (D : SphereHyperbolicMetricData A), E.card ≤ q →
        D.pole = (∞ : OnePoint ℂ) →
        sphereHyperbolicAreaGain A hA
          ((A ∪ K) ∪ sphereFiniteSet E)
          ((hA.union hK.isClosed).union
            (E.finite_toSet.image
              (fun z : ℂ => ((z : ℂ) : OnePoint ℂ))).isClosed)
          (subset_union_left.trans subset_union_left) D L ≤ C := by
  obtain ⟨M,hMtop,hM⟩ := uniform_compact_gain_sphere hK hL hKL
  let cost : ℝ≥0∞ := (q : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi)
  refine ⟨M + cost, ENNReal.add_ne_top.mpr
    ⟨hMtop, ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top⟩, ?_⟩
  intro E A hA D hEq hpole
  let B : Set (OnePoint ℂ) := A ∪ K
  let C : Set (OnePoint ℂ) := B ∪ sphereFiniteSet E
  have hB : IsClosed B := hA.union hK.isClosed
  have hE : IsClosed (sphereFiniteSet E) :=
    (E.finite_toSet.image
      (fun z : ℂ => ((z : ℂ) : OnePoint ℂ))).isClosed
  have hC : IsClosed C := hB.union hE
  let DB : SphereHyperbolicMetricData B := D.mono subset_union_left
  have hDBpole : DB.pole = (∞ : OnePoint ℂ) := hpole
  have hcompact := hM A hA D
  have hfiniteUniv := sphere_finite_removal_gain_le_two_pi_mul_card
    hB DB hDBpole E
  have hfiniteL : sphereHyperbolicAreaGain B hB C hC subset_union_left DB L ≤ cost := by
    calc
      sphereHyperbolicAreaGain B hB C hC subset_union_left DB L ≤
          (E.card : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi) := by
            apply hfiniteUniv.trans'
            unfold sphereHyperbolicAreaGain
            apply lintegral_mono_set
            intro z hz
            exact ⟨Set.mem_univ _, hz.2⟩
      _ ≤ cost := mul_le_mul_right' (ENNReal.natCast_le_natCast.mpr hEq) _
  have htrans := sphereHyperbolicAreaGain_trans hA hB hC
    subset_union_left subset_union_left D (W := L)
  change sphereHyperbolicAreaGain A hA C hC
      (subset_union_left.trans subset_union_left) D L ≤ M + cost
  exact htrans.trans (add_le_add hcompact hfiniteL)

end AreaDeficit

#print axioms AreaDeficit.uniform_compact_finite_gain_sphere
#print axioms AreaDeficit.uniform_compact_finite_gain_sphere_le
