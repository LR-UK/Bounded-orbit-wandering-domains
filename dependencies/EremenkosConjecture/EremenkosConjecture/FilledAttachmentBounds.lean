import EremenkosConjecture.FilledAttachmentDomains
import ComplexApproximation.Topology.FillingCoordinateBounds
import FunctionTheory.Conformal.StripCoordinates

open Set Metric Complex

namespace EremenkosConjecture

theorem strict_im_bound_of_open {U : Set ℂ} {c H : ℝ}
    (hU : IsOpen U) (hbound : ∀ z ∈ U, |z.im - c| ≤ H) :
    ∀ z ∈ U, |z.im - c| < H := by
  intro z hz
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z hz
  have ht : 0 < ε / 2 := half_pos hε
  have htε : ε / 2 < ε := half_lt_self hε
  have hplus : z + ((ε / 2 : ℝ) : ℂ) * I ∈ U := by
    apply hball
    simpa [mem_ball, dist_eq_norm, norm_mul, abs_of_pos hε] using htε
  have hminus : z - ((ε / 2 : ℝ) : ℂ) * I ∈ U := by
    apply hball
    simpa [mem_ball, dist_eq_norm, norm_mul, abs_of_pos hε] using htε
  have hp := (abs_le.mp (hbound _ hplus)).2
  have hm := (abs_le.mp (hbound _ hminus)).1
  simp only [add_im, sub_im, mul_im, ofReal_re, I_im, mul_one,
    ofReal_im, I_re, mul_zero, add_zero] at hp hm
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- Filling the attachment preserves the common strip and left bounds;
openness makes the strip inequality strict on the selected domain. -/
theorem filledAttachmentDomain_coordinate_bounds
    {C : Set ℂ} {ζ a : ℂ} {s η H L : ℝ}
    (hCim : ∀ z ∈ C, |z.im - a.im| ≤ H)
    (hCre : ∀ z ∈ C, L ≤ z.re)
    (hη : η ≤ H) (him : ζ.im = a.im)
    (hζL : L ≤ ζ.re - s) (haL : L ≤ a.re) :
    ∀ z ∈ filledAttachmentDomain C ζ a s η H,
      L ≤ z.re ∧ |z.im - a.im| < H := by
  have hEim : ∀ z ∈ attachedHalfStrips C ζ a s η H, |z.im - a.im| ≤ H := by
    rintro z ((hz | hz) | hz)
    · exact hCim z hz
    · exact (by simpa only [him] using hz.2 : |z.im - a.im| ≤ η).trans hη
    · exact hz.2
  have hEre : ∀ z ∈ attachedHalfStrips C ζ a s η H, L ≤ z.re := by
    rintro z ((hz | hz) | hz)
    · exact hCre z hz
    · exact hζL.trans hz.1
    · exact haL.trans (by simpa only [sub_zero] using hz.1)
  have hsub : filledAttachmentDomain C ζ a s η H ⊆
      ComplexApproximation.fill (attachedHalfStrips C ζ a s η H) :=
    (connectedComponentIn_subset _ _).trans interior_subset
  have hi := strict_im_bound_of_open isOpen_interior.connectedComponentIn
    (fun z hz => ComplexApproximation.fill_preserves_im_bound hEim z (hsub hz))
  exact fun z hz => ⟨ComplexApproximation.fill_preserves_re_lower_bound hEre z (hsub hz), hi z hz⟩

/-- Beyond the junction, the domain contains the entire straight open tail. -/
theorem straight_tail_subset_filledAttachmentDomain
    {C : Set ℂ} {ζ a : ℂ} {s η H : ℝ}
    (hC : IsConnected (interior C)) (hζ : ζ ∈ interior C)
    (hs : 0 < s) (hη : 0 < η) (hH : 0 < H) (him : ζ.im = a.im) :
    {z : ℂ | a.re < z.re ∧ |z.im - a.im| < H} ⊆
      filledAttachmentDomain C ζ a s η H := by
  intro z hz
  apply attachmentCore_subset_filledAttachmentDomain hC hζ hs hη hH him
  exact Or.inr (mem_interior_closedHalfStrip_of_strict (by simpa using hz.1) hz.2)

end EremenkosConjecture
