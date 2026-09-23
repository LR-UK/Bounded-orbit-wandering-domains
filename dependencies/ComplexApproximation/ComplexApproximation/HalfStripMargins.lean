import ComplexApproximation.Topology.HalfStripBands

/-! # Uniform neighbourhoods of half-strips and their boundary bands -/

open Set Metric Complex
open scoped Topology

namespace ComplexApproximation

theorem openRightHalfStrip_subset_interior (a b : ℝ) :
    openRightHalfStrip a b ⊆ interior (closedRightHalfStrip a b) := by
  intro z hz
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset ((isOpen_openRightHalfStrip a b).mem_nhds hz)
    (fun _ hw => ⟨hw.1.le, hw.2.le⟩)

theorem frontier_closedRightHalfStrip_subset {a b : ℝ} {z : ℂ}
    (hz : z ∈ frontier (closedRightHalfStrip a b)) :
    z ∈ closedRightHalfStrip a b ∧ (z.re = a ∨ |z.im| = b) := by
  have hmem : z ∈ closedRightHalfStrip a b :=
    (isClosed_closedRightHalfStrip a b).closure_eq ▸ hz.1
  refine ⟨hmem, ?_⟩
  have hn : ¬ (a < z.re ∧ |z.im| < b) := fun h =>
    hz.2 (openRightHalfStrip_subset_interior a b h)
  rcases hmem.1.eq_or_lt with h | h
  · exact Or.inl h.symm
  · exact Or.inr (le_antisymm hmem.2 (le_of_not_gt (fun hi => hn ⟨h, hi⟩)))

theorem ball_subset_openRightHalfStrip {a b r : ℝ} {z : ℂ}
    (hre : a + r ≤ z.re) (him : |z.im| + r ≤ b) :
    ball z r ⊆ openRightHalfStrip a b := by
  intro w hw
  have hd : ‖w - z‖ < r := by simpa only [mem_ball, dist_eq_norm] using hw
  have hr := abs_lt.mp ((Complex.abs_re_le_norm (w - z)).trans_lt hd)
  have hi := (Complex.abs_im_le_norm (w - z)).trans_lt hd
  simp only [Complex.sub_re, Complex.sub_im] at hr hi
  constructor
  · linarith [hr.1]
  · have h := abs_add_le (w.im - z.im) z.im
    rw [sub_add_cancel] at h
    linarith

theorem ball_frontier_subset_halfStripBand {a₀ a a₁ b₀ b b₁ r : ℝ}
    (hra₀ : r ≤ a - a₀) (hra₁ : r ≤ a₁ - a)
    (hrb₀ : r ≤ b₀ - b) (hrb₁ : r ≤ b - b₁)
    {z : ℂ} (hz : z ∈ frontier (closedRightHalfStrip a b)) :
    ball z r ⊆ halfStripBand a₀ a₁ b₀ b₁ := by
  obtain ⟨hzmem, hzboundary⟩ := frontier_closedRightHalfStrip_subset hz
  intro w hw
  have hd : ‖w - z‖ < r := by simpa only [mem_ball, dist_eq_norm] using hw
  have hr := abs_lt.mp ((Complex.abs_re_le_norm (w - z)).trans_lt hd)
  have hi := (Complex.abs_im_le_norm (w - z)).trans_lt hd
  simp only [Complex.sub_re, Complex.sub_im] at hr hi
  have hwre : a₀ ≤ w.re := by linarith [hr.1, hzmem.1]
  have hwim : |w.im| ≤ b₀ := by
    have h := abs_add_le (w.im - z.im) z.im
    rw [sub_add_cancel] at h
    linarith [hzmem.2]
  refine ⟨⟨hwre, hwim⟩, ?_⟩
  intro hwinner
  rcases hzboundary with hzre | hzim
  · linarith [hwinner.1, hr.2]
  · have h := abs_add_le (z.im - w.im) w.im
    rw [sub_add_cancel, abs_sub_comm] at h
    linarith [hwinner.2]

theorem exists_frontier_tube_in_halfStripBand {a₀ a a₁ b₀ b b₁ : ℝ}
    (ha₀ : a₀ < a) (ha₁ : a < a₁) (hb₀ : b < b₀) (hb₁ : b₁ < b) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ frontier (closedRightHalfStrip a b),
      ball z r ⊆ halfStripBand a₀ a₁ b₀ b₁ := by
  let r := min (min (a - a₀) (a₁ - a)) (min (b₀ - b) (b - b₁))
  have hr : 0 < r := lt_min (lt_min (sub_pos.mpr ha₀) (sub_pos.mpr ha₁))
    (lt_min (sub_pos.mpr hb₀) (sub_pos.mpr hb₁))
  refine ⟨r, hr, fun _ hz => ball_frontier_subset_halfStripBand ?_ ?_ ?_ ?_ hz⟩
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

end ComplexApproximation
