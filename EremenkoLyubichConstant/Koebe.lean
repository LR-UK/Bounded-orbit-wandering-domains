/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

import Ray.Koebe.Koebe

/-!
# The Koebe quarter theorem

The statement is given using Mathlib's `DifferentiableOn` and `Set.InjOn` interfaces.
The proof applies Geoffrey Irving's `koebe_quarter` theorem from `Ray.Koebe.Koebe`
directly, converting differentiability on the open disc to analyticity there.
Ray supplies the complete Grönwall--Bieberbach--Koebe proof.
-/

open Set Metric

namespace EremenkoLyubichConstant

noncomputable section

/-- The open unit disc. -/
abbrev unitDisc : Set ℂ := ball 0 1

/-- Koebe's one-quarter theorem, in a scale-invariant form. -/
theorem koebe_quarter
    {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g unitDisc)
    (hinj : Set.InjOn g unitDisc) :
    ball (g 0) (‖deriv g 0‖ / 4) ⊆ g '' unitDisc := by
  exact _root_.koebe_quarter
    (Complex.analyticOnNhd_iff_differentiableOn isOpen_ball |>.2 hg) hinj

/-- Omitted-point form of Koebe: the distance to any omitted value controls the derivative. -/
theorem norm_deriv_le_four_mul_of_omits
    {g : ℂ → ℂ} {w : ℂ}
    (hg : DifferentiableOn ℂ g unitDisc)
    (hinj : Set.InjOn g unitDisc)
    (hw : w ∉ g '' unitDisc) :
    ‖deriv g 0‖ ≤ 4 * ‖w - g 0‖ := by
  by_contra h
  have hlt : ‖w - g 0‖ < ‖deriv g 0‖ / 4 := by
    have hfour : (0 : ℝ) < 4 := by norm_num
    have := lt_of_not_ge h
    nlinarith
  have hmem : w ∈ ball (g 0) (‖deriv g 0‖ / 4) := by
    simpa [mem_ball, dist_eq_norm] using hlt
  exact hw (koebe_quarter hg hinj hmem)

/-- Normalised omitted-zero form used in the proof of the Eremenko--Lyubich estimate. -/
theorem norm_deriv_le_four_of_eq_one_omits_zero
    {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g unitDisc)
    (hinj : Set.InjOn g unitDisc)
    (hg0 : g 0 = 1)
    (homit : (0 : ℂ) ∉ g '' unitDisc) :
    ‖deriv g 0‖ ≤ 4 := by
  simpa [hg0] using norm_deriv_le_four_mul_of_omits hg hinj homit

end

end EremenkoLyubichConstant
