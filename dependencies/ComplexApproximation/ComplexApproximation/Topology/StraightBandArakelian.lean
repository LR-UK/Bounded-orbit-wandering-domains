import ComplexApproximation.Topology.HalfStripBands
import ComplexApproximation.Topology.ArakelianHomeomorphism
import ComplexApproximation.Topology.ArakelianElementaryGeometry
import FunctionTheory.Conformal.StripBounds

open Set Metric Complex Bornology

namespace ComplexApproximation

/-- A closed set with no bounded holes and the straight tail of a band plus
an inner halfstrip is Arakelian. The bounded decoration is unrestricted. -/
theorem isArakelian_of_straight_band_tail
    {E : Set ℂ} {L M A c b₀ b₁ b₂ : ℝ}
    (hE : IsClosed E) (hfull : NoBoundedComplementComponents E)
    (hleft : ∀ z ∈ E, L ≤ z.re) (him : ∀ z ∈ E, |z.im| ≤ M)
    (hb₂ : 0 ≤ b₂) (hb₁ : b₂ < b₁) (hb₀ : b₁ < b₀)
    (htail : ∀ z : ℂ, A < z.re →
      (z ∈ E ↔ (b₁ ≤ |z.im - c| ∧ |z.im - c| ≤ b₀) ∨ |z.im - c| ≤ b₂)) :
    IsArakelian E := by
  let H : ℂ ≃ₜ ℂ := Homeomorph.addRight ((c : ℂ) * I)
  let F := H '' bandAndHalfStrip (A - 3) (A - 2) (A - 1) b₀ b₁ b₂
  have hF : IsArakelian F := (isArakelian_bandAndHalfStrip
    (by linarith : A - 3 < A - 2) (by linarith : A - 2 < A - 1) hb₂ hb₁ hb₀).image_homeomorph H
  have hHre z : (H z).re = z.re := by simp [H]
  have hHim z : (H z).im = z.im + c := by simp [H]
  have hFbounds : ∀ z ∈ F, A - 3 ≤ z.re ∧ |z.im| ≤ b₀ + |c| := by
    rintro _ ⟨w, hw, rfl⟩
    have hwre : A - 3 ≤ w.re := by
      rcases hw with hw | hw
      · exact hw.1.1
      · linarith [hw.1]
    have hwim : |w.im| ≤ b₀ := by
      rcases hw with hw | hw
      · exact hw.1.2
      · exact hw.2.trans (hb₁.trans hb₀).le
    rw [hHre, hHim]
    exact ⟨hwre, (abs_add_le _ _).trans (by linarith)⟩
  have hFtail : ∀ z : ℂ, A < z.re →
      (z ∈ F ↔ (b₁ ≤ |z.im - c| ∧ |z.im - c| ≤ b₀) ∨ |z.im - c| ≤ b₂) := by
    intro z hzA
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hHre] at hzA
      simp only [hHim, add_sub_cancel_right]
      rcases hw with hw | hw
      · left
        refine ⟨le_of_not_gt (fun h => hw.2 ⟨by linarith, h⟩), hw.1.2⟩
      · exact Or.inr hw.2
    · intro hz
      let w : ℂ := ⟨z.re, z.im - c⟩
      have heq : H w = z := by apply Complex.ext <;> simp [hHre, hHim, w]
      refine ⟨w, ?_, heq⟩
      rcases hz with hz | hz
      · exact Or.inl ⟨⟨by dsimp [w]; linarith, hz.2⟩,
          fun h => not_lt_of_ge hz.1 h.2⟩
      · exact Or.inr ⟨by dsimp [w]; linarith, hz⟩
  have hEc := FunctionTheory.isCompact_left_truncation_of_strip_bounds
    (R := A) hE hleft him
  have hFc := FunctionTheory.isCompact_left_truncation_of_strip_bounds
    (R := A) hF.isClosed (fun z hz => (hFbounds z hz).1) (fun z hz => (hFbounds z hz).2)
  apply hF.of_bounded_modification hE hfull
  · apply hEc.isBounded.subset
    intro z hz
    refine ⟨hz.1, ?_⟩
    change z.re ≤ A
    apply le_of_not_gt
    intro hAz
    exact hz.2 ((hFtail z hAz).mpr ((htail z hAz).mp hz.1))
  · apply hFc.isBounded.subset
    intro z hz
    refine ⟨hz.1, ?_⟩
    change z.re ≤ A
    apply le_of_not_gt
    intro hAz
    exact hz.2 ((htail z hAz).mpr ((hFtail z hAz).mp hz.1))

end ComplexApproximation
