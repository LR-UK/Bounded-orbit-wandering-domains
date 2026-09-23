import EremenkosConjecture.FilledRayInterior
import EremenkosConjecture.FilledRayArakelian
import ComplexApproximation.Topology.StraightBandArakelian

open Set Metric Complex Bornology

namespace EremenkosConjecture

/-- The actual approximation band and inner inset form an Arakelian set.
The open middle set is its ray-containing component; no assertion about all
other components of its interior is needed. -/
theorem isArakelian_filledRayBand_union_inner
    {C₀ C₁ C₂ : Set ℂ} {ζ : ℂ} {s₀ s₁ s₂ η₀ η₁ η₂ : ℝ}
    (hC₀ : IsCompact C₀) (hC₁ : IsCompact C₁) (hC₂ : IsCompact C₂)
    (hC₂conn : IsConnected C₂) (hζ₂ : ζ ∈ C₂)
    (hC₁₀ : C₁ ⊆ interior C₀) (hC₂₁ : C₂ ⊆ interior C₁)
    (hs₂ : 0 < s₂) (hs₂₁ : s₂ < s₁) (hs₁₀ : s₁ < s₀)
    (hη₂ : 0 < η₂) (hη₂₁ : η₂ < η₁) (hη₁₀ : η₁ < η₀) :
    ComplexApproximation.IsArakelian
      ((filledRayInset C₀ ζ s₀ η₀ \ filledRayInterior C₁ ζ s₁ η₁) ∪
        filledRayInset C₂ ζ s₂ η₂) := by
  let P := filledRayInset C₀ ζ s₀ η₀
  let U := filledRayInterior C₁ ζ s₁ η₁
  let B := filledRayInset C₂ ζ s₂ η₂
  have hs₁ : 0 < s₁ := hs₂.trans hs₂₁
  have hs₀ : 0 < s₀ := hs₁.trans hs₁₀
  have hη₁ : 0 < η₁ := hη₂.trans hη₂₁
  have hη₀ : 0 < η₀ := hη₁.trans hη₁₀
  have hP := isArakelian_filledRayInset (ζ := ζ) hC₀ hs₀.le hη₀.le
  have hB := isArakelian_filledRayInset (ζ := ζ) hC₂ hs₂.le hη₂.le
  have hU := filledRayInterior_properties C₁ ζ hs₁ hη₁
  have hBprops := filledRayInset_properties (X := ∅) hC₂ hC₂conn hζ₂ (empty_subset _) hs₂ hη₂
  have hBmiddle : B ⊆ interior (filledRayInset C₁ ζ s₁ η₁) :=
    filledRayInset_subset_interior_of_nested hC₂.isClosed hC₂₁ hs₂₁ hη₂₁
  have hBU : B ⊆ U := hBprops.2.2.1.isPreconnected.subset_connectedComponentIn
    (ComplexApproximation.subset_fill _ (Or.inl hζ₂)) hBmiddle
  have hUP : U ⊆ P := (connectedComponentIn_subset _ _).trans
    (interior_subset.trans ((filledRayInset_subset_interior_of_nested hC₁.isClosed hC₁₀ hs₁₀ hη₁₀).trans interior_subset))
  obtain ⟨L₂, H₂, A₂, _, hζA₂, hbounds₂, htail₂⟩ :=
    exists_filledRayInset_bounds (ζ := ζ) (η := η₂) hC₂ hs₂.le
  let q : ℂ := ⟨A₂ + 1, ζ.im + (η₁ + η₂) / 2⟩
  have hgap : ¬ IsBounded (U \ B) := by
    have hray : ∀ t : ℝ, 0 ≤ t → q + (t : ℂ) ∈ U \ B := by
      intro t ht
      have hre : (q + (t : ℂ)).re = A₂ + 1 + t := by simp [q]
      have him : |(q + (t : ℂ)).im - ζ.im| = (η₁ + η₂) / 2 := by
        simp only [add_im, ofReal_im, add_zero, q, add_sub_cancel_left]
        exact abs_of_pos (by linarith)
      refine ⟨?_, ?_⟩
      · apply interior_halfStrip_subset_filledRayInterior C₁ ζ hs₁ hη₁
        apply mem_interior_closedHalfStrip_of_strict
        · rw [hre]; linarith
        · rw [him]; linarith
      · intro hzB
        have hi := (htail₂ _ (by rw [hre]; linarith)).mp hzB
        rw [him] at hi
        linarith
    have hunb := ComplexApproximation.not_isBounded_component_of_right_ray hray
    exact fun hb => hunb (hb.subset (connectedComponentIn_subset _ _))
  have hfull := ComplexApproximation.noBoundedComplementComponents_band_union_inner
    hP.noBoundedComplementComponents hU.1 hU.2.1.isPreconnected hB.isClosed
    (isConnected_compl_filledRayInset (ζ := ζ) (η := η₂) hC₂ hs₂.le).isPreconnected hBU hUP hgap
  obtain ⟨L₀, H₀, A₀, _, _, hbounds₀, htail₀⟩ :=
    exists_filledRayInset_bounds (ζ := ζ) (η := η₀) hC₀ hs₀.le
  obtain ⟨L₁, H₁, A₁, _, hζA₁, _, htail₁⟩ :=
    exists_filledRayInset_bounds (ζ := ζ) (η := η₁) hC₁ hs₁.le
  have hUtail := filledRayInterior_tail_iff hs₁ hη₁ hζA₁ htail₁
  let A := max A₀ (max A₁ A₂)
  have hEP : (P \ U) ∪ B ⊆ P := union_subset sdiff_subset (hBU.trans hUP)
  apply ComplexApproximation.isArakelian_of_straight_band_tail
    (L := L₀) (M := H₀ + |ζ.im|) (A := A) (c := ζ.im)
    (b₀ := η₀) (b₁ := η₁) (b₂ := η₂)
    ((hP.isClosed.sdiff hU.1).union hB.isClosed) hfull
    (fun z hz => (hbounds₀ z (hEP hz)).1) ?_ hη₂.le hη₂₁ hη₁₀ ?_
  · intro z hz
    have hi := abs_le.mp (hbounds₀ z (hEP hz)).2
    apply abs_le.mpr
    constructor <;> linarith [hi.1, hi.2, neg_abs_le ζ.im, le_abs_self ζ.im]
  · intro z hzA
    have hz₀ : A₀ < z.re := (le_max_left _ _).trans_lt hzA
    have hz₁ : A₁ < z.re := ((le_max_left A₁ A₂).trans (le_max_right _ _)).trans_lt hzA
    have hz₂ : A₂ < z.re := ((le_max_right A₁ A₂).trans (le_max_right _ _)).trans_lt hzA
    change ((z ∈ P ∧ z ∉ U) ∨ z ∈ B) ↔ _
    rw [htail₀ z hz₀, hUtail z hz₁, htail₂ z hz₂]
    simp only [not_lt, and_comm]

end EremenkosConjecture
