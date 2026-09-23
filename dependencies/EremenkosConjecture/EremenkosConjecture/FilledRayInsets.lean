import EremenkosConjecture.HalfStripInterior
import ComplexApproximation.Topology.FillingInterior
import ComplexApproximation.Topology.FillingCoordinateBounds

open Set Metric Complex

namespace EremenkosConjecture

/-- A closed neighbourhood of a compact decoration with a straight ray tail. -/
def filledRayInset (C : Set ℂ) (ζ : ℂ) (s η : ℝ) : Set ℂ :=
  ComplexApproximation.fill (C ∪ closedHalfStrip ζ s η)

theorem filledRayInset_properties {C X : Set ℂ} {ζ : ℂ} {s η : ℝ}
    (hC : IsCompact C) (hCc : IsConnected C) (hζ : ζ ∈ C)
    (hXC : X ⊆ interior C) (hs : 0 < s) (hη : 0 < η) :
    IsClosed (filledRayInset C ζ s η) ∧
      ComplexApproximation.NoBoundedComplementComponents (filledRayInset C ζ s η) ∧
      IsConnected (filledRayInset C ζ s η) ∧
      X ∪ horizontalRay ζ ⊆ interior (filledRayInset C ζ s η) := by
  have hclosed := hC.isClosed.union (isClosed_closedHalfStrip ζ s η)
  have hζS : ζ ∈ closedHalfStrip ζ s η :=
    interior_subset (horizontalRay_subset_interior_halfStrip hs hη (mem_horizontalRay ζ))
  refine ⟨ComplexApproximation.isClosed_fill hclosed,
    ComplexApproximation.noBoundedComplementComponents_fill _,
    ComplexApproximation.isConnected_fill hclosed
      (hCc.union ⟨ζ, hζ, hζS⟩ ((convex_closedHalfStrip ζ s η).isConnected ⟨ζ, hζS⟩)), ?_⟩
  rintro z (hz | hz)
  · exact interior_mono
      (fun w hw => ComplexApproximation.subset_fill _ (Or.inl hw)) (hXC hz)
  · exact interior_mono
      (fun w hw => ComplexApproximation.subset_fill _ (Or.inr hw))
      (horizontalRay_subset_interior_halfStrip hs hη hz)

/-- Once past the compact decoration and the beginning of the halfstrip,
filling changes nothing: the closed inset has an exactly straight tail. -/
theorem filledRayInset_tail_iff {C : Set ℂ} {ζ z : ℂ} {s η A : ℝ}
    (hC : ∀ w ∈ C, w.re ≤ A) (hzA : A < z.re) (hzs : ζ.re - s ≤ z.re) :
    z ∈ filledRayInset C ζ s η ↔ |z.im - ζ.im| ≤ η := by
  constructor
  · intro hz
    apply ComplexApproximation.fill_preserves_channel_in_vertical_slab
      (A := A) (B := z.re + 1) (E := C ∪ closedHalfStrip ζ s η) ?_ z hz hzA (by linarith)
    rintro w (hw | hw) hwA _
    · exact False.elim ((not_lt_of_ge (hC w hw)) hwA)
    · exact hw.2
  · intro hz
    exact ComplexApproximation.subset_fill _ (Or.inr ⟨hzs, hz⟩)

theorem filledRayInset_subset_interior {C F : Set ℂ} {ζ : ℂ} {s η : ℝ}
    (hC : IsClosed C) (hCF : C ⊆ interior F)
    (hSF : closedHalfStrip ζ s η ⊆ interior F)
    (hF : ComplexApproximation.NoBoundedComplementComponents F) :
    filledRayInset C ζ s η ⊆ interior F :=
  ComplexApproximation.fill_subset_interior_of_noBoundedComplementComponents
    (hC.union (isClosed_closedHalfStrip ζ s η)) (union_subset hCF hSF) hF

theorem filledRayInset_coordinate_bounds {C : Set ℂ} {ζ : ℂ} {s η L H : ℝ}
    (hCre : ∀ z ∈ C, L ≤ z.re) (hCim : ∀ z ∈ C, |z.im - ζ.im| ≤ H)
    (hLs : L ≤ ζ.re - s) (hηH : η ≤ H) :
    ∀ z ∈ filledRayInset C ζ s η, L ≤ z.re ∧ |z.im - ζ.im| ≤ H := by
  intro z hz
  constructor
  · apply ComplexApproximation.fill_preserves_re_lower_bound (E := C ∪ closedHalfStrip ζ s η) ?_ z hz
    rintro w (hw | hw)
    · exact hCre w hw
    · exact hLs.trans hw.1
  · apply ComplexApproximation.fill_preserves_im_bound (E := C ∪ closedHalfStrip ζ s η) ?_ z hz
    rintro w (hw | hw)
    · exact hCim w hw
    · exact hw.2.trans hηH

end EremenkosConjecture
