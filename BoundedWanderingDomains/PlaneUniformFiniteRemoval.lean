/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.AreaAnchorFree

/-! # Uniform compact and finite removal in arbitrary plane domains -/

open Set MeasureTheory
open scoped ENNReal

namespace AreaDeficit

/-- Plane form of the paper's area lemma. The old hyperbolic domain may vary,
the exceptional points may move, and only their cardinality bound enters the
constant. -/
theorem uniform_compact_finite_gain_plane
    (q : ℕ) {K L : Set ℂ} (hK : IsCompact K) (hL : IsCompact L)
    (hLK : Disjoint L K) :
    ∃ T : ℝ≥0∞, T ≠ ∞ ∧
      ∀ (A : Set ℂ) (hA : IsClosed A) {c d : ℂ} (hcd : c ≠ d) (hc : c ∈ A) (hd : d ∈ A),
        ∀ E : Finset ℂ, E.card ≤ q →
          (∫⁻ z in L ∩ (A ∪ K ∪ (↑E : Set ℂ))ᶜ,
            hyperbolicAreaWeight (A ∪ K ∪ (↑E : Set ℂ))
                ((hA.union hK.isClosed).union E.finite_toSet.isClosed)
                hcd (Or.inl (Or.inl hc)) (Or.inl (Or.inl hd)) z -
              hyperbolicAreaWeight A hA hcd hc hd z) ≤ T := by
  obtain ⟨C,hC,hcompact⟩ := uniform_compact_gain_plane hL hK hLK
  let P : ℝ≥0∞ := (q : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi)
  have hP : P ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top q) ENNReal.ofReal_ne_top
  refine ⟨C + P, ENNReal.add_ne_top.mpr ⟨hC,hP⟩, ?_⟩
  intro A hA c d hcd hc hd E hEq
  let B : Set ℂ := A ∪ K
  let D : Set ℂ := B ∪ (↑E : Set ℂ)
  have hB : IsClosed B := hA.union hK.isClosed
  have hD : IsClosed D := hB.union E.finite_toSet.isClosed
  have hBc : c ∈ B := Or.inl hc
  have hBd : d ∈ B := Or.inl hd
  have hDc : c ∈ D := Or.inl hBc
  have hDd : d ∈ D := Or.inl hBd
  let W : Set ℂ := L ∩ Dᶜ
  have hmeas : AEMeasurable (fun z =>
      hyperbolicAreaWeight D hD hcd hDc hDd z -
        hyperbolicAreaWeight B hB hcd hBc hBd z) (volume.restrict W) :=
    (((((measurable_closedComplementDensity D hD hcd hDc hDd).pow_const 2).ennreal_ofReal).sub
      (((measurable_closedComplementDensity B hB hcd hBc hBd).pow_const 2).ennreal_ofReal)).aemeasurable)
  have hsplit :
      (∫⁻ z in W, hyperbolicAreaWeight D hD hcd hDc hDd z -
          hyperbolicAreaWeight A hA hcd hc hd z) ≤
        (∫⁻ z in W, hyperbolicAreaWeight D hD hcd hDc hDd z -
          hyperbolicAreaWeight B hB hcd hBc hBd z) +
        (∫⁻ z in W, hyperbolicAreaWeight B hB hcd hBc hBd z -
          hyperbolicAreaWeight A hA hcd hc hd z) := by
    exact lintegral_gain_le_gain_add_gain _ _ _ _
      (Filter.Eventually.of_forall (fun _ => le_rfl)) hmeas
  have hfinite :
      (∫⁻ z in W, hyperbolicAreaWeight D hD hcd hDc hDd z -
          hyperbolicAreaWeight B hB hcd hBc hBd z) ≤ P := by
    calc
      (∫⁻ z in W, hyperbolicAreaWeight D hD hcd hDc hDd z -
          hyperbolicAreaWeight B hB hcd hBc hBd z) ≤
          ∫⁻ z in Dᶜ, hyperbolicAreaWeight D hD hcd hDc hDd z -
            hyperbolicAreaWeight B hB hcd hBc hBd z := by
              apply lintegral_mono_set
              exact fun _ hz => hz.2
      _ ≤ (E.card : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi) := by
          simpa only [B, D] using
            finite_removal_gain_le_two_pi_mul_card B hB E hcd hBc hBd
      _ ≤ P := by
        dsimp only [P]
        gcongr
  have hremote :
      (∫⁻ z in W, hyperbolicAreaWeight B hB hcd hBc hBd z -
          hyperbolicAreaWeight A hA hcd hc hd z) ≤ C := by
    calc
      (∫⁻ z in W, hyperbolicAreaWeight B hB hcd hBc hBd z -
          hyperbolicAreaWeight A hA hcd hc hd z) ≤
          ∫⁻ z in L ∩ Aᶜ, hyperbolicAreaWeight B hB hcd hBc hBd z -
            hyperbolicAreaWeight A hA hcd hc hd z := by
              apply lintegral_mono_set
              intro z hz
              exact ⟨hz.1, fun hzA => hz.2 (Or.inl (Or.inl hzA))⟩
      _ ≤ C := by simpa only [B] using hcompact A hA hcd hc hd
  change (∫⁻ z in W, hyperbolicAreaWeight D hD hcd hDc hDd z -
    hyperbolicAreaWeight A hA hcd hc hd z) ≤ C + P
  exact hsplit.trans ((add_le_add hfinite hremote).trans_eq (add_comm P C))

end AreaDeficit

#print axioms AreaDeficit.uniform_compact_finite_gain_plane
