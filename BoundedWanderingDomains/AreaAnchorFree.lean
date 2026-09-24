/- 
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.AreaAnchorIndependence
import BoundedWanderingDomains.UnnormalisedPointRemoval

/-!
# Uniform compact-removal area bound for plane domains

Insert two fixed auxiliary omitted values into each old obstacle, invoke
the anchored cutoff estimate, then charge their insertion to the proved
finite-puncture bound. The old domain may have infinite hyperbolic area.
All integrals use the curvature −1 hyperbolic area form.
-/

open Set MeasureTheory
open scoped ENNReal

namespace AreaDeficit

/-- A finite area-gain bound depending only on two disjoint compact planar
sets, uniformly over every hyperbolic old domain. -/
theorem uniform_compact_gain_plane
    {W K : Set ℂ} (hW : IsCompact W) (hK : IsCompact K)
    (hWK : Disjoint W K) :
    ∃ T : ℝ≥0∞, T ≠ ⊤ ∧ ∀ (A : Set ℂ) (hA : IsClosed A)
      {c d : ℂ} (hcd : c ≠ d) (hc : c ∈ A) (hd : d ∈ A),
      (∫⁻ z in W ∩ Aᶜ,
        hyperbolicAreaWeight (A ∪ K) (hA.union hK.isClosed)
          hcd (Or.inl hc) (Or.inl hd) z -
        hyperbolicAreaWeight A hA hcd hc hd z) ≤ T := by
  let E : Finset ℂ := {0, 1}
  have h01 : (0 : ℂ) ≠ 1 := by norm_num
  obtain ⟨T, hTf, hT⟩ :=
    uniform_closed_compact_gain_anchored hW hK hWK h01
  let cost : ℝ≥0∞ := (E.card : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi)
  have hcost : cost ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  refine ⟨T + cost, ENNReal.add_ne_top.mpr ⟨hTf, hcost⟩, ?_⟩
  intro A hA c d hcd hc hd
  let P : Set ℂ := A ∪ (↑E : Set ℂ)
  let B : Set ℂ := A ∪ K
  let Q : Set ℂ := P ∪ K
  have hP : IsClosed P := hA.union E.finite_toSet.isClosed
  have hB : IsClosed B := hA.union hK.isClosed
  have hQ : IsClosed Q := hP.union hK.isClosed
  have hP0 : (0 : ℂ) ∈ P := Or.inr (by simp [E])
  have hP1 : (1 : ℂ) ∈ P := Or.inr (by simp [E])
  have hPc : c ∈ P := Or.inl hc
  have hPd : d ∈ P := Or.inl hd
  have hBc : c ∈ B := Or.inl hc
  have hBd : d ∈ B := Or.inl hd
  have hQ0 : (0 : ℂ) ∈ Q := Or.inl hP0
  have hQ1 : (1 : ℂ) ∈ Q := Or.inl hP1
  have hanch :
      (∫⁻ z in W ∩ Pᶜ,
        hyperbolicAreaWeight Q hQ h01 hQ0 hQ1 z -
        hyperbolicAreaWeight P hP h01 hP0 hP1 z) ≤ T :=
    hT P hP hP0 hP1
  have hpunct :
      (∫⁻ z in Pᶜ,
        hyperbolicAreaWeight P hP hcd hPc hPd z -
        hyperbolicAreaWeight A hA hcd hc hd z) ≤ cost :=
    finite_removal_gain_le_two_pi_mul_card A hA E hcd hc hd
  have hD : MeasurableSet (W ∩ Pᶜ) := hW.measurableSet.inter hP.isOpen_compl.measurableSet
  have hBQ : B ⊆ Q := by
    intro x hx
    rcases hx with hxA | hxK
    · exact Or.inl (Or.inl hxA)
    · exact Or.inr hxK
  have hpoint : ∀ᵐ z : ℂ ∂volume.restrict (W ∩ Pᶜ),
      hyperbolicAreaWeight B hB hcd hBc hBd z ≤
        hyperbolicAreaWeight Q hQ h01 hQ0 hQ1 z := by
    filter_upwards [ae_restrict_mem hD] with z hz
    have hzQ : z ∉ Q := by
      intro hzQ
      rcases hzQ with hzP | hzK
      · exact hz.2 hzP
      · exact Set.disjoint_left.mp hWK hz.1 hzK
    exact hyperbolicAreaWeight_mono_any B Q hB hQ hBQ
      hcd h01 hBc hBd hQ0 hQ1 hzQ
  have hmeas : AEMeasurable (fun z =>
      hyperbolicAreaWeight Q hQ h01 hQ0 hQ1 z -
      hyperbolicAreaWeight P hP h01 hP0 hP1 z)
        (volume.restrict (W ∩ Pᶜ)) := by
    apply Measurable.aemeasurable
    exact ((((measurable_closedComplementDensity Q hQ h01 hQ0 hQ1).pow_const 2).ennreal_ofReal).sub
      (((measurable_closedComplementDensity P hP h01 hP0 hP1).pow_const 2).ennreal_ofReal))
  have hgain :
      (∫⁻ z in W ∩ Pᶜ,
        hyperbolicAreaWeight B hB hcd hBc hBd z -
        hyperbolicAreaWeight A hA hcd hc hd z) ≤ T + cost := by
    have hsub := lintegral_gain_le_gain_add_gain
      (hyperbolicAreaWeight B hB hcd hBc hBd)
      (hyperbolicAreaWeight Q hQ h01 hQ0 hQ1)
      (hyperbolicAreaWeight P hP h01 hP0 hP1)
      (hyperbolicAreaWeight A hA hcd hc hd) hpoint hmeas
    have hother :
        (∫⁻ z in W ∩ Pᶜ,
          hyperbolicAreaWeight P hP h01 hP0 hP1 z -
          hyperbolicAreaWeight A hA hcd hc hd z) ≤ cost := by
      calc
        (∫⁻ z in W ∩ Pᶜ,
          hyperbolicAreaWeight P hP h01 hP0 hP1 z -
          hyperbolicAreaWeight A hA hcd hc hd z) =
          (∫⁻ z in W ∩ Pᶜ,
            hyperbolicAreaWeight P hP hcd hPc hPd z -
            hyperbolicAreaWeight A hA hcd hc hd z) := by
              apply lintegral_congr
              intro z
              rw [show hyperbolicAreaWeight P hP h01 hP0 hP1 z =
                hyperbolicAreaWeight P hP hcd hPc hPd z from
                  closedComplementHyperbolicAreaWeight_anchor_independent
                    P hP h01 hcd hP0 hP1 hPc hPd z]
        _ ≤ (∫⁻ z in Pᶜ,
            hyperbolicAreaWeight P hP hcd hPc hPd z -
            hyperbolicAreaWeight A hA hcd hc hd z) := by
              apply lintegral_mono_set
              intro z hz
              exact hz.2
        _ ≤ cost := hpunct
    exact hsub.trans (add_le_add hanch hother)
  calc
    (∫⁻ z in W ∩ Aᶜ,
      hyperbolicAreaWeight (A ∪ K) (hA.union hK.isClosed)
        hcd (Or.inl hc) (Or.inl hd) z -
      hyperbolicAreaWeight A hA hcd hc hd z) =
      (∫⁻ z in W ∩ Pᶜ,
        hyperbolicAreaWeight B hB hcd hBc hBd z -
        hyperbolicAreaWeight A hA hcd hc hd z) := by
          change (∫⁻ z, hyperbolicAreaWeight B hB hcd hBc hBd z -
            hyperbolicAreaWeight A hA hcd hc hd z ∂(volume.restrict (W ∩ Aᶜ))) =
            (∫⁻ z, hyperbolicAreaWeight B hB hcd hBc hBd z -
              hyperbolicAreaWeight A hA hcd hc hd z ∂(volume.restrict (W ∩ Pᶜ)))
          rw [(restrict_complement_union_finite W A E).symm]
    _ ≤ T + cost := hgain

end AreaDeficit

#print axioms AreaDeficit.uniform_compact_gain_plane
