import FunctionTheory.Conformal.StripCoordinates

/-! # Finite boundary coordinates of a horizontal strip

The inverse strip-to-disk coordinate is continuous on the closed strip and
avoids the boundary point one. A homeomorphic disk boundary map taking one
to zero therefore gives a continuous logarithmic inverse on the closed strip.
This supplies an individual-map interface, not a family-convergence assertion.
-/

open Set Metric Complex

namespace FunctionTheory

def closedHorizontalStrip : Set ℂ := {z | |z.im| ≤ Real.pi / 2}

noncomputable def horizontalStripToDisc (z : ℂ) : ℂ := cayleyCoordinate (exp (-z))

theorem re_exp_neg_nonneg_of_mem_closedStrip {z : ℂ} (hz : z ∈ closedHorizontalStrip) :
    0 ≤ (exp (-z)).re := by
  rw [exp_re, neg_re, neg_im, Real.cos_neg]
  exact mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc (abs_le.mp hz))

theorem horizontalStripToDisc_mem_closedBall {z : ℂ} (hz : z ∈ closedHorizontalStrip) :
    horizontalStripToDisc z ∈ closedBall 0 1 :=
  cayleyCoordinate_mem_closedBall (re_exp_neg_nonneg_of_mem_closedStrip hz)

theorem horizontalStripToDisc_ne_one {z : ℂ} (hz : z ∈ closedHorizontalStrip) :
    horizontalStripToDisc z ≠ 1 := by
  intro h
  have hd := cayley_denominator_ne_zero (re_exp_neg_nonneg_of_mem_closedStrip hz)
  have heq : cayleyCoordinate (exp (-z)) = cayleyCoordinate 0 := by
    simpa only [horizontalStripToDisc, cayleyCoordinate_zero] using h
  have he := cayleyCoordinate_injOn hd (by simp) heq
  exact exp_ne_zero (-z) he

theorem continuousOn_horizontalStripToDisc :
    ContinuousOn horizontalStripToDisc closedHorizontalStrip := by
  have hc : ContinuousOn cayleyCoordinate {w : ℂ | 0 ≤ w.re} := fun w hw =>
    (differentiableAt_cayleyCoordinate
      (cayley_denominator_ne_zero hw)).continuousAt.continuousWithinAt
  exact hc.comp (continuous_exp.comp continuous_neg).continuousOn
    (fun _ hz => re_exp_neg_nonneg_of_mem_closedStrip hz)

theorem horizontalStripToDisc_mem_ball {z : ℂ} (hz : z ∈ standardHorizontalStrip) :
    horizontalStripToDisc z ∈ ball 0 1 :=
  cayleyCoordinate_mem_ball (re_exp_neg_pos_of_mem_strip hz)

theorem discToHorizontalStrip_horizontalStripToDisc {z : ℂ}
    (hz : z ∈ standardHorizontalStrip) :
    discToHorizontalStrip (horizontalStripToDisc z) = z := by
  change -log (cayleyCoordinate (cayleyCoordinate (exp (-z)))) = z
  rw [cayleyCoordinate_involution (cayley_denominator_ne_zero
    (re_exp_neg_pos_of_mem_strip hz).le)]
  exact neg_log_exp_neg_of_mem_strip hz

theorem continuousOn_logarithmic_strip_inverse {G : ℂ → ℂ}
    (hGc : ContinuousOn G (closedBall 0 1)) (hGi : InjOn G (closedBall 0 1))
    (hG1 : G 1 = 0) (hGre : ∀ w ∈ closedBall (0 : ℂ) 1, 0 ≤ (G w).re) :
    ContinuousOn (fun z => -log (G (horizontalStripToDisc z))) closedHorizontalStrip := by
  have hGslit : MapsTo (fun z => G (horizontalStripToDisc z))
      closedHorizontalStrip slitPlane := by
    intro z hz
    have hmem := horizontalStripToDisc_mem_closedBall hz
    have hne : G (horizontalStripToDisc z) ≠ 0 := by
      intro h
      exact horizontalStripToDisc_ne_one hz
        (hGi hmem (by simp) (h.trans hG1.symm))
    rw [mem_slitPlane_iff]
    by_cases hpos : 0 < (G (horizontalStripToDisc z)).re
    · exact Or.inl hpos
    · right
      intro him
      apply hne
      apply Complex.ext
      · exact le_antisymm (le_of_not_gt hpos) (hGre _ hmem)
      · exact him
  have hlog : ContinuousOn (fun w => -log w) slitPlane := fun w hw =>
    (differentiableAt_log hw).neg.continuousAt.continuousWithinAt
  exact hlog.comp (hGc.comp continuousOn_horizontalStripToDisc
    (fun _ hz => horizontalStripToDisc_mem_closedBall hz)) hGslit

end FunctionTheory
