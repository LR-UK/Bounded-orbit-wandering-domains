import EremenkosConjecture.RayGeometry
import FunctionTheory.Conformal.StripUniformity

open Set Metric Complex

namespace EremenkosConjecture

/-- A compact set with a horizontal ray has a uniform neighbourhood inside
any open neighbourhood that contains a straight tail of positive width. -/
theorem exists_uniform_tube_of_compact_union_horizontalRay
    {X U : Set ℂ} {ζ : ℂ} {R H : ℝ}
    (hX : IsCompact X) (hU : IsOpen U) (hXU : X ∪ horizontalRay ζ ⊆ U)
    (hH : 0 < H)
    (htail : ∀ z : ℂ, R < z.re → |z.im - ζ.im| < H → z ∈ U) :
    ∃ ε > 0, ∀ z ∈ X ∪ horizontalRay ζ, closedBall z ε ⊆ U := by
  obtain ⟨B, hB⟩ := hX.isBounded.subset_closedBall (0 : ℂ)
  have hnorm : ∀ z ∈ X, ‖z‖ ≤ B := fun z hz => by
    simpa only [mem_closedBall, dist_zero_right] using hB hz
  have hleft : ∀ z ∈ X ∪ horizontalRay ζ, min (-B) ζ.re ≤ z.re := by
    rintro z (hz | hz)
    · have hb := (abs_le.mp ((abs_re_le_norm z).trans (hnorm z hz))).1
      exact (min_le_left _ _).trans hb
    · exact (min_le_right _ _).trans hz.1
  have him : ∀ z ∈ X ∪ horizontalRay ζ, |z.im| ≤ max B |ζ.im| := by
    rintro z (hz | hz)
    · exact ((abs_im_le_norm z).trans (hnorm z hz)).trans (le_max_left _ _)
    · rw [hz.2]; exact le_max_right _ _
  let δ := min H 1 / 2
  have hδ : 0 < δ := half_pos (lt_min hH zero_lt_one)
  have hδH : δ < H := (half_lt_self (lt_min hH zero_lt_one)).trans_le (min_le_left _ _)
  have hδ1 : δ < 1 := (half_lt_self (lt_min hH zero_lt_one)).trans_le (min_le_right _ _)
  apply FunctionTheory.exists_uniform_neighbourhood_of_strip_tail
    (R := max B R + 1) (hX.isClosed.union (isClosed_horizontalRay ζ)) hleft him hU hXU hδ
  intro z hz hzR w hw
  have hzray : z ∈ horizontalRay ζ := by
    rcases hz with hz | hz
    · have hb := (re_le_norm z).trans (hnorm z hz)
      linarith [le_max_left B R]
    · exact hz
  have hd : ‖w - z‖ ≤ δ := by simpa only [mem_closedBall, dist_eq_norm] using hw
  have hre : |w.re - z.re| ≤ δ := by
    simpa only [sub_re] using (abs_re_le_norm (w - z)).trans hd
  have him' : |w.im - ζ.im| ≤ δ := by
    simpa only [sub_im, hzray.2] using (abs_im_le_norm (w - z)).trans hd
  exact htail w (by linarith [(abs_le.mp hre).1, le_max_right B R]) (him'.trans_lt hδH)

/-- A uniform tube around a horizontal ray contains a closed halfstrip of
positive width, including a small extension to the left of the endpoint. -/
theorem exists_closed_halfStrip_subset_of_uniform_tube
    {U : Set ℂ} {ζ : ℂ} {ε : ℝ} (hε : 0 < ε)
    (htube : ∀ z ∈ horizontalRay ζ, closedBall z ε ⊆ U) :
    ∃ t > 0, closedHalfStrip ζ t t ⊆ U := by
  refine ⟨ε / 4, by positivity, ?_⟩
  intro z hz
  let w : ℂ := ⟨max ζ.re z.re, ζ.im⟩
  have hw : w ∈ horizontalRay ζ := ⟨le_max_left _ _, rfl⟩
  apply htube w hw
  have hre : |z.re - w.re| ≤ ε / 4 := by
    rw [abs_of_nonpos (by dsimp [w]; exact sub_nonpos.mpr (le_max_right _ _))]
    dsimp [w]
    rcases le_total ζ.re z.re with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith [hz.1]
  have him : |z.im - w.im| ≤ ε / 4 := hz.2
  rw [mem_closedBall, dist_eq_norm]
  exact (norm_le_abs_re_add_abs_im (z - w)).trans
    (by simpa only [sub_re, sub_im] using (show |z.re - w.re| + |z.im - w.im| ≤ ε by linarith))

end EremenkosConjecture
