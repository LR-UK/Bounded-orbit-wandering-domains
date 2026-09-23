import EremenkosConjecture.FilledRayComplement
import EremenkosConjecture.FilledAttachmentBounds

open Set Metric Complex

namespace EremenkosConjecture

/-- The component containing the attached ray inside a filled closed inset. -/
def filledRayInterior (C : Set ℂ) (ζ : ℂ) (s η : ℝ) : Set ℂ :=
  connectedComponentIn (interior (filledRayInset C ζ s η)) ζ

theorem interior_halfStrip_subset_filledRayInterior
    (C : Set ℂ) (ζ : ℂ) {s η : ℝ} (hs : 0 < s) (hη : 0 < η) :
    interior (closedHalfStrip ζ s η) ⊆ filledRayInterior C ζ s η :=
  (isConnected_interior_closedHalfStrip ζ s hη).isPreconnected.subset_connectedComponentIn
    (horizontalRay_subset_interior_halfStrip hs hη (mem_horizontalRay ζ))
    (interior_mono (fun _ hz => ComplexApproximation.subset_fill _ (Or.inr hz)))

theorem filledRayInterior_properties (C : Set ℂ) (ζ : ℂ) {s η : ℝ}
    (hs : 0 < s) (hη : 0 < η) :
    IsOpen (filledRayInterior C ζ s η) ∧ IsConnected (filledRayInterior C ζ s η) ∧
      horizontalRay ζ ⊆ filledRayInterior C ζ s η := by
  have hsub := interior_halfStrip_subset_filledRayInterior C ζ hs hη
  have hray := (horizontalRay_subset_interior_halfStrip hs hη).trans hsub
  refine ⟨isOpen_interior.connectedComponentIn, ?_, hray⟩
  apply isConnected_connectedComponentIn_iff.mpr
  exact connectedComponentIn_subset _ _ (hray (mem_horizontalRay ζ))

/-- The selected interior component has the expected open straight tail,
even if other interior components were not ruled out globally. -/
theorem filledRayInterior_tail_iff {C : Set ℂ} {ζ : ℂ} {s η A : ℝ}
    (hs : 0 < s) (hη : 0 < η) (hζA : ζ.re ≤ A)
    (htail : ∀ z : ℂ, A < z.re → (z ∈ filledRayInset C ζ s η ↔ |z.im - ζ.im| ≤ η)) :
    ∀ z : ℂ, A < z.re → (z ∈ filledRayInterior C ζ s η ↔ |z.im - ζ.im| < η) := by
  have ho := (filledRayInterior_properties C ζ hs hη).1
  have hstrict : ∀ z ∈ filledRayInterior C ζ s η ∩ {w : ℂ | A < w.re},
      |z.im - ζ.im| < η := by
    apply strict_im_bound_of_open (ho.inter (isOpen_lt continuous_const continuous_re))
    intro z hz
    exact (htail z hz.2).mp (interior_subset (connectedComponentIn_subset _ _ hz.1))
  intro z hzA
  constructor
  · intro hz
    exact hstrict z ⟨hz, hzA⟩
  · intro hz
    apply interior_halfStrip_subset_filledRayInterior C ζ hs hη
    exact mem_interior_closedHalfStrip_of_strict (by linarith) hz

theorem filledRayInset_subset_interior_of_nested
    {C D : Set ℂ} {ζ : ℂ} {s t η κ : ℝ}
    (hC : IsClosed C) (hCD : C ⊆ interior D) (hst : s < t) (hηκ : η < κ) :
    filledRayInset C ζ s η ⊆ interior (filledRayInset D ζ t κ) := by
  apply filledRayInset_subset_interior hC
    (hCD.trans (interior_mono (fun _ hz => ComplexApproximation.subset_fill _ (Or.inl hz))))
    ?_ (ComplexApproximation.noBoundedComplementComponents_fill _)
  intro z hz
  apply interior_mono (fun _ hw => ComplexApproximation.subset_fill _ (Or.inr hw))
  exact mem_interior_closedHalfStrip_of_strict (by linarith [hz.1]) (hz.2.trans_lt hηκ)

end EremenkosConjecture
