import ComplexApproximation.Topology.Arakelian
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Topological invariance of the planar Arakelian condition -/

open Set Metric Bornology

namespace ComplexApproximation

theorem isBounded_image_continuous {F : ℂ → ℂ} (hF : Continuous F) {E : Set ℂ}
    (hE : IsBounded E) : IsBounded (F '' E) :=
  (hE.isCompact_closure.image hF).isBounded.subset (image_mono subset_closure)

theorem isBounded_image_homeomorph_iff (H : ℂ ≃ₜ ℂ) (E : Set ℂ) :
    IsBounded (H '' E) ↔ IsBounded E := by
  constructor
  · intro h
    have hh := isBounded_image_continuous H.symm.continuous h
    simpa [image_image] using hh
  · exact isBounded_image_continuous H.continuous

theorem mem_fill_image_homeomorph_iff (H : ℂ ≃ₜ ℂ) (E : Set ℂ) (z : ℂ) :
    H z ∈ fill (H '' E) ↔ z ∈ fill E := by
  by_cases hz : z ∈ E
  · exact iff_of_true (subset_fill _ (mem_image_of_mem H hz)) (subset_fill _ hz)
  · have he : H '' connectedComponentIn Eᶜ z =
        connectedComponentIn (H '' E)ᶜ (H z) := by
      have hh := H.image_connectedComponentIn (s := Eᶜ) (x := z) hz
      have hc : H '' Eᶜ = (H '' E)ᶜ := H.toEquiv.image_compl E
      rwa [hc] at hh
    change IsBounded (connectedComponentIn (H '' E)ᶜ (H z)) ↔
      IsBounded (connectedComponentIn Eᶜ z)
    rw [← he]
    exact isBounded_image_homeomorph_iff H _

theorem fill_image_homeomorph (H : ℂ ≃ₜ ℂ) (E : Set ℂ) :
    fill (H '' E) = H '' fill E := by
  ext w
  constructor
  · intro hw
    refine ⟨H.symm w, ?_, H.apply_symm_apply w⟩
    apply (mem_fill_image_homeomorph_iff H E (H.symm w)).mp
    simpa only [H.apply_symm_apply] using hw
  · rintro ⟨z, hz, rfl⟩
    exact (mem_fill_image_homeomorph_iff H E z).mpr hz

/-- The no-holes and bounded-exhaustion-holes formulation is invariant under
homeomorphisms of the plane. No metric bounds on the homeomorphism are needed. -/
theorem IsArakelian.image_homeomorph {E : Set ℂ} (hE : IsArakelian E) (H : ℂ ≃ₜ ℂ) :
    IsArakelian (H '' E) := by
  refine ⟨H.isClosedMap E hE.isClosed, ?_, ?_⟩
  · intro w hw hbound
    have hpre : H.symm w ∉ E := fun hz => hw ⟨H.symm w, hz, H.apply_symm_apply w⟩
    apply hE.noBoundedComplementComponents (H.symm w) hpre
    apply (mem_fill_image_homeomorph_iff H E (H.symm w)).mp
    simpa only [H.apply_symm_apply, fill, mem_ofPred_eq] using hbound
  · intro R
    have hpre : IsBounded (H.symm '' closedBall 0 R) :=
      ((isCompact_closedBall 0 R).image H.symm.continuous).isBounded
    obtain ⟨r, hr, hbound⟩ := hpre.exists_pos_norm_le
    have hsub : H '' E ∪ closedBall 0 R ⊆ H '' (E ∪ closedBall 0 r) := by
      rintro w (hw | hw)
      · exact image_mono subset_union_left hw
      · refine ⟨H.symm w, Or.inr ?_, H.apply_symm_apply w⟩
        exact mem_closedBall_zero_iff.mpr (hbound _ (mem_image_of_mem H.symm hw))
    have hfill := fill_mono hsub
    rw [fill_image_homeomorph] at hfill
    apply (isBounded_image_continuous H.continuous (hE.boundedHoles r)).subset
    rintro w ⟨hw, hwE⟩
    obtain ⟨z, hz, rfl⟩ := hfill hw
    exact ⟨z, ⟨hz, fun hzE => hwE (mem_image_of_mem H hzE)⟩, rfl⟩

end ComplexApproximation
