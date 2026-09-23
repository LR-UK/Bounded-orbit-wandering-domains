import EremenkosConjecture.QuantitativeGeometry
import ComplexApproximation.HalfStripApproximation

/-! # The Arakelian set at one stage of the ray construction -/

open Set Metric Function
open scoped NNReal

namespace EremenkosConjecture

open Scaffolding ComplexApproximation

def rayBand (a b : ℝ) : Set ℂ := translation rayBase ''
  halfStripBand (-(3 * a / 2)) (-(a / 2)) (3 * b / 2) (b / 2)

theorem isClosed_rayBand (a b : ℝ) : IsClosed (rayBand a b) :=
  (translation rayBase).isClosedMap _
    ((isClosed_closedRightHalfStrip _ _).sdiff (isOpen_openRightHalfStrip _ _))

theorem rayBand_subset_halfStrip {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    rayBand a b ⊆ closedHalfStrip rayBase (2 * a) (2 * b) := by
  rintro _ ⟨z, hz, rfl⟩
  constructor
  · change rayBase.re - 2 * a ≤ z.re + rayBase.re
    linarith [hz.1.1]
  · simpa only [translation_apply, Complex.add_im, add_sub_cancel_right] using
      hz.1.2.trans (show 3 * b / 2 ≤ 2 * b by linarith)

theorem disjoint_rayBand_inner {a b η : ℝ} (hη : η < a) (hb : 0 < b) :
    Disjoint (rayBand a b) (closedHalfStrip rayBase (η / 2) (b / 4)) := by
  apply disjoint_left.mpr
  rintro _ ⟨z, hz, rfl⟩ hinner
  apply hz.2
  constructor
  · have hr := hinner.1
    change rayBase.re - η / 2 ≤ z.re + rayBase.re at hr
    linarith
  · have hi := hinner.2
    simp only [translation_apply, Complex.add_im, add_sub_cancel_right] at hi
    exact hi.trans_lt (by linarith)

theorem hasUniformTube_frontier_rayBand {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasUniformTube (frontier (closedHalfStrip rayBase a b)) (rayBand a b) := by
  have h := exists_frontier_tube_in_halfStripBand
    (show -(3 * a / 2) < -a by linarith) (show -a < -(a / 2) by linarith)
    (show b < 3 * b / 2 by linarith) (show b / 2 < b by linarith)
  have ht : HasUniformTube (frontier (closedRightHalfStrip (-a) b))
      (halfStripBand (-(3 * a / 2)) (-(a / 2)) (3 * b / 2) (b / 2)) := h
  have hi := ht.image (translation rayBase) (lipschitz_translation_symm rayBase)
  simpa only [Homeomorph.image_frontier, translation_image_halfStrip, rayBand] using hi

namespace RayStage

theorem inner_subset_region {j : ℕ} (S : RayStage j) {η : ℝ} (hη : η < S.a) :
    closedHalfStrip rayBase (η / 2) (S.b / 4) ⊆ S.region := by
  intro z hz
  exact ⟨by linarith [hz.1, S.a_pos], hz.2.trans (by linarith [S.b_pos])⟩

theorem isArakelian_configuration {j : ℕ} (S : RayStage j)
    (H : ℂ ≃ₜ ℂ) (heH : EqOn (S.f^[returnTime j]) H S.region)
    {η : ℝ} (hη : 0 < η) (hηa : η < S.a) :
    IsArakelian ((background j ∪ H '' rayBand S.a S.b) ∪
      H '' closedHalfStrip rayBase (η / 2) (S.b / 4)) := by
  obtain ⟨d, hd, hmargin⟩ := S.targetMargin
  let Q := (translation rayBase).trans H
  have hband : Q '' bandAndHalfStrip (-(3 * S.a / 2)) (-(S.a / 2)) (-(η / 2))
      (3 * S.b / 2) (S.b / 2) (S.b / 4) ⊆
      {z | (height j + 7) / 4 + d ≤ z.im ∧ z.im ≤ (height j + 11) / 4 - d} := by
    rintro _ ⟨z, hz, rfl⟩
    have hreg : translation rayBase z ∈ S.region := by
      rcases hz with hz | hz
      · exact rayBand_subset_halfStrip S.a_pos.le S.b_pos.le ⟨z, hz, rfl⟩
      · apply S.inner_subset_region hηa
        rw [← translation_image_halfStrip]
        exact ⟨z, hz, rfl⟩
    change (height j + 7) / 4 + d ≤ (H (translation rayBase z)).im ∧
      (H (translation rayBase z)).im ≤ (height j + 11) / 4 - d
    rw [← heH hreg]
    exact hmargin _ hreg
  have hg : Disjoint (horizontalLift (backgroundLevels j))
      (openHorizontalStrip ((height j + 7) / 4) ((height j + 11) / 4)) := by
    rw [← background_eq_horizontalLift, ← targetStrip_eq_openHorizontalStrip]
    exact disjoint_background_targetStrip j
  have hArak := isArakelian_horizontal_background_union_image_band
    (show -(3 * S.a / 2) < -(S.a / 2) by linarith [S.a_pos])
    (show -(S.a / 2) < -(η / 2) by linarith)
    (show 0 ≤ S.b / 4 by linarith [S.b_pos])
    (show S.b / 4 < S.b / 2 by linarith [S.b_pos])
    (show S.b / 2 < 3 * S.b / 2 by linarith [S.b_pos]) Q
    (isClosed_backgroundLevels j) (show (height j + 7) / 4 < (height j + 7) / 4 + d by linarith)
    (show (height j + 11) / 4 - d < (height j + 11) / 4 by linarith) hband hg
  have hQB : Q '' halfStripBand (-(3 * S.a / 2)) (-(S.a / 2)) (3 * S.b / 2) (S.b / 2) =
      H '' rayBand S.a S.b := by
    exact (image_image H (translation rayBase) _).symm
  have hQC : Q '' closedRightHalfStrip (-(η / 2)) (S.b / 4) =
      H '' closedHalfStrip rayBase (η / 2) (S.b / 4) := by
    change (fun z => H (translation rayBase z)) '' _ = _
    rw [← image_image H (translation rayBase), translation_image_halfStrip]
  rwa [hQB, hQC, ← background_eq_horizontalLift] at hArak

theorem configuration_subset_next_background {j : ℕ} (S : RayStage j)
    (H : ℂ ≃ₜ ℂ) (heH : EqOn (S.f^[returnTime j]) H S.region)
    {η : ℝ} (hηa : η < S.a) :
    (background j ∪ H '' rayBand S.a S.b) ∪
      H '' closedHalfStrip rayBase (η / 2) (S.b / 4) ⊆ background (j + 1) := by
  have hT : H '' S.region ⊆ background (j + 1) := by
    rintro _ ⟨z, hz, rfl⟩
    apply ball_target_subset_next_background (j := j) (z := H z) _ (mem_ball_self (by norm_num))
    rw [← heH hz]
    exact S.mapsTo_region_target hz
  rintro z ((hz | hz) | hz)
  · exact background_monotone (Nat.le_succ j) hz
  · exact hT (image_mono (rayBand_subset_halfStrip S.a_pos.le S.b_pos.le) hz)
  · exact hT (image_mono (S.inner_subset_region hηa) hz)

end RayStage

end EremenkosConjecture
