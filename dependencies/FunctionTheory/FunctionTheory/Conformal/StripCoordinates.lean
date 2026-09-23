import FunctionTheory.Conformal.CayleyCoordinates
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Explicit conformal coordinates for the horizontal strip -/

open Set Metric Complex

namespace FunctionTheory

def standardHorizontalStrip : Set ℂ := {z | |z.im| < Real.pi / 2}

theorem isOpen_standardHorizontalStrip : IsOpen standardHorizontalStrip :=
  isOpen_lt Complex.continuous_im.abs continuous_const

theorem re_exp_neg_pos_of_mem_strip {z : ℂ} (hz : z ∈ standardHorizontalStrip) :
    0 < (exp (-z)).re := by
  rw [exp_re, neg_re, neg_im, Real.cos_neg]
  exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo (abs_lt.mp hz))

theorem neg_log_mem_strip {w : ℂ} (hw : 0 < w.re) : -log w ∈ standardHorizontalStrip := by
  change |(-log w).im| < Real.pi / 2
  rw [neg_im, abs_neg, log_im]
  exact abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)

theorem neg_log_exp_neg_of_mem_strip {z : ℂ} (hz : z ∈ standardHorizontalStrip) :
    -log (exp (-z)) = z := by
  have hbounds := abs_lt.mp (show |z.im| < Real.pi / 2 from hz)
  rw [log_exp (by simp only [neg_im]; linarith [Real.pi_pos])
    (by simp only [neg_im]; linarith [Real.pi_pos]), neg_neg]

theorem exp_neg_neg_log_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    exp (-(-log w)) = w := by
  rw [neg_neg, exp_log]
  intro h
  simp [h] at hw

theorem bijOn_exp_neg_strip :
    BijOn (fun z => exp (-z)) standardHorizontalStrip {w : ℂ | 0 < w.re} := by
  refine ⟨fun _ hz => re_exp_neg_pos_of_mem_strip hz, ?_, ?_⟩
  · intro z hz w hw heq
    have h := congrArg (fun v => -log v) heq
    simpa only [neg_log_exp_neg_of_mem_strip hz, neg_log_exp_neg_of_mem_strip hw] using h
  · intro w hw
    exact ⟨-log w, neg_log_mem_strip hw, exp_neg_neg_log_of_re_pos hw⟩

theorem bijOn_neg_log_rightHalfPlane :
    BijOn (fun w => -log w) {w : ℂ | 0 < w.re} standardHorizontalStrip := by
  refine ⟨fun _ hw => neg_log_mem_strip hw, ?_, ?_⟩
  · intro z hz w hw heq
    have h := congrArg (fun v => exp (-v)) heq
    simpa only [exp_neg_neg_log_of_re_pos hz, exp_neg_neg_log_of_re_pos hw] using h
  · intro z hz
    exact ⟨exp (-z), re_exp_neg_pos_of_mem_strip hz, neg_log_exp_neg_of_mem_strip hz⟩

theorem differentiableOn_neg_log_rightHalfPlane :
    DifferentiableOn ℂ (fun w => -log w) {w : ℂ | 0 < w.re} := by
  intro w hw
  exact (differentiableAt_log (mem_slitPlane_iff.mpr (Or.inl hw))).neg.differentiableWithinAt

noncomputable def discToHorizontalStrip (w : ℂ) : ℂ := -log (cayleyCoordinate w)

theorem bijOn_discToHorizontalStrip :
    BijOn discToHorizontalStrip (ball 0 1) standardHorizontalStrip :=
  bijOn_neg_log_rightHalfPlane.comp bijOn_cayleyCoordinate_ball

theorem differentiableOn_discToHorizontalStrip :
    DifferentiableOn ℂ discToHorizontalStrip (ball 0 1) := by
  apply differentiableOn_neg_log_rightHalfPlane.comp
    (fun z hz => (differentiableAt_cayleyCoordinate
      (cayley_denominator_ne_zero_of_mem_ball hz)).differentiableWithinAt)
    bijOn_cayleyCoordinate_ball.mapsTo

@[simp] theorem discToHorizontalStrip_zero : discToHorizontalStrip 0 = 0 := by
  simp [discToHorizontalStrip]

theorem exp_neg_discToHorizontalStrip {w : ℂ} (hw : w ∈ ball 0 1) :
    exp (-discToHorizontalStrip w) = cayleyCoordinate w :=
  exp_neg_neg_log_of_re_pos (re_cayleyCoordinate_pos_of_mem_ball hw)

end FunctionTheory
