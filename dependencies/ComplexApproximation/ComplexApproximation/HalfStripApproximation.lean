import ComplexApproximation.ArakelianGluing
import ComplexApproximation.Topology.ArakelianHomeomorphism
import ComplexApproximation.Topology.StripArakelian
import ComplexApproximation.Topology.HalfStripBands

/-! # Arakelian approximation on the model Section 7 configuration -/

open Set Complex

namespace ComplexApproximation

theorem isArakelian_horizontal_background_union_image_band
    {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ} (ha₀ : a₀ < a₁) (ha₁ : a₁ < a₂)
    (hb₂ : 0 ≤ b₂) (hb₁ : b₂ < b₁) (hb₀ : b₁ < b₀)
    (H : ℂ ≃ₜ ℂ) {A : Set ℝ} (hA : IsClosed A)
    {l u a b : ℝ} (hla : l < a) (hbu : b < u)
    (hband : H '' bandAndHalfStrip a₀ a₁ a₂ b₀ b₁ b₂ ⊆ {z | a ≤ z.im ∧ z.im ≤ b})
    (hgap : Disjoint (horizontalLift A) (openHorizontalStrip l u)) :
    IsArakelian ((horizontalLift A ∪ H '' halfStripBand a₀ a₁ b₀ b₁) ∪
      H '' closedRightHalfStrip a₂ b₂) := by
  have hF := (isArakelian_bandAndHalfStrip ha₀ ha₁ hb₂ hb₁ hb₀).image_homeomorph H
  have hf := hF.union_horizontal_background hA hla hbu hband hgap
  simpa only [bandAndHalfStrip, image_union, union_assoc] using hf

theorem arakelian_approximation_halfStrip_configuration
    {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ} (ha₀ : a₀ < a₁) (ha₁ : a₁ < a₂)
    (hb₂ : 0 ≤ b₂) (hb₁ : b₂ < b₁) (hb₀ : b₁ < b₀)
    (H : ℂ ≃ₜ ℂ) {A : Set ℝ} (hA : IsClosed A)
    {l u a b : ℝ} (hla : l < a) (hbu : b < u)
    (hband : H '' bandAndHalfStrip a₀ a₁ a₂ b₀ b₁ b₂ ⊆ {z | a ≤ z.im ∧ z.im ≤ b})
    (hgap : Disjoint (horizontalLift A) (openHorizontalStrip l u))
    (U V W : Set ℂ) (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (hAU : horizontalLift A ⊆ U) (hBV : H '' halfStripBand a₀ a₁ b₀ b₁ ⊆ V)
    (hCW : H '' closedRightHalfStrip a₂ b₂ ⊆ W)
    (f g h : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (hg : DifferentiableOn ℂ g V) (hh : DifferentiableOn ℂ h W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ z ∈ horizontalLift A, ‖f z - F z‖ < ε) ∧
      (∀ z ∈ H '' halfStripBand a₀ a₁ b₀ b₁, ‖g z - F z‖ < ε) ∧
      (∀ z ∈ H '' closedRightHalfStrip a₂ b₂, ‖h z - F z‖ < ε) := by
  have hB : IsClosed (halfStripBand a₀ a₁ b₀ b₁) :=
    (isClosed_closedRightHalfStrip a₀ b₀).sdiff (isOpen_openRightHalfStrip a₁ b₁)
  have hBC : Disjoint (halfStripBand a₀ a₁ b₀ b₁) (closedRightHalfStrip a₂ b₂) := by
    apply disjoint_left.mpr
    rintro z ⟨_, hn⟩ ⟨hr, hi⟩
    exact hn ⟨ha₁.trans_le hr, hi.trans_lt hb₁⟩
  have hsub : H '' bandAndHalfStrip a₀ a₁ a₂ b₀ b₁ b₂ ⊆ openHorizontalStrip l u :=
    fun z hz => ⟨hla.trans_le (hband hz).1, (hband hz).2.trans_lt hbu⟩
  have hd : Disjoint (horizontalLift A) (H '' bandAndHalfStrip a₀ a₁ a₂ b₀ b₁ b₂) :=
    hgap.mono_right hsub
  have hd' : Disjoint (horizontalLift A) (H '' halfStripBand a₀ a₁ b₀ b₁) ∧
      Disjoint (horizontalLift A) (H '' closedRightHalfStrip a₂ b₂) := by
    simpa only [bandAndHalfStrip, image_union, disjoint_union_right] using hd
  have hdBC : Disjoint (H '' halfStripBand a₀ a₁ b₀ b₁) (H '' closedRightHalfStrip a₂ b₂) := by
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    exact disjoint_left.mp hBC hx ((H.injective he) ▸ hy)
  apply arakelian_approximation_three_pieces _ _ _ U V W
    (hA.preimage Complex.continuous_im) (H.isClosedMap _ hB)
    (H.isClosedMap _ (isClosed_closedRightHalfStrip a₂ b₂)) hd'.1 hd'.2
    hdBC
    (isArakelian_horizontal_background_union_image_band ha₀ ha₁ hb₂ hb₁ hb₀ H hA hla hbu hband hgap)
    hU hV hW hAU hBV hCW f g h hf hg hh hε

end ComplexApproximation
