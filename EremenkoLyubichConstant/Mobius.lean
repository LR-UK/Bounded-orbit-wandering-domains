/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

import EremenkoLyubichConstant.Koebe

/-! # The disc-to-right-half-plane Möbius transformation -/

open Set Metric
open scoped Topology

namespace EremenkoLyubichConstant

noncomputable section

/-- The Möbius map `(1-z)/(1+z)` from the unit disc to the right half-plane. -/
def discToRight (z : ℂ) : ℂ := (1 - z) / (1 + z)

/-- The denominator of `discToRight` does not vanish on the unit disc. -/
lemma one_add_ne_zero_of_mem_unitDisc {z : ℂ} (hz : z ∈ unitDisc) : 1 + z ≠ 0 := by
  have hn : ‖z‖ < 1 := by simpa [unitDisc, mem_ball] using hz
  intro h
  have hz' : z = -1 := by linear_combination h
  simp [hz'] at hn

/-- `discToRight` is injective on the unit disc. -/
lemma discToRight_injective : Set.InjOn discToRight unitDisc := by
  intro x hx y hy h
  have hx0 := one_add_ne_zero_of_mem_unitDisc hx
  have hy0 := one_add_ne_zero_of_mem_unitDisc hy
  simp only [discToRight] at h
  field_simp at h
  have h' : 2 * x = 2 * y := by linear_combination -h
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h'

/-- The derivative of `discToRight` at zero is `-2`. -/
lemma hasDerivAt_discToRight_zero : HasDerivAt discToRight (-2) 0 := by
  have h :=
    ((hasDerivAt_const (x := (0 : ℂ)) 1).sub (hasDerivAt_id (𝕜 := ℂ) 0)).div
      ((hasDerivAt_const (x := (0 : ℂ)) 1).add (hasDerivAt_id (𝕜 := ℂ) 0)) (by norm_num)
  have hfun : discToRight = ((fun _ : ℂ => 1) - id) / ((fun _ : ℂ => 1) + id) := by
    funext z
    rfl
  rw [hfun]
  convert h using 1; norm_num

/-- `discToRight` maps the unit disc into the open right half-plane. -/
lemma discToRight_maps (z : ℂ) (hz : z ∈ unitDisc) : 0 < (discToRight z).re := by
  have hn : ‖z‖ < 1 := by simpa [unitDisc, mem_ball] using hz
  have hsq : z.re ^ 2 + z.im ^ 2 < 1 := by
    calc
      z.re ^ 2 + z.im ^ 2 = Complex.normSq z := by simp [Complex.normSq, pow_two]
      _ = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
      _ < 1 := by nlinarith [mul_self_lt_mul_self (norm_nonneg z) hn]
  have hden : 0 < (1 + z.re) ^ 2 + z.im ^ 2 := by
    have hne := one_add_ne_zero_of_mem_unitDisc hz
    calc
      0 < Complex.normSq (1 + z) := Complex.normSq_pos.mpr hne
      _ = (1 + z.re) ^ 2 + z.im ^ 2 := by simp [Complex.normSq, pow_two]
  have hnormSq : Complex.normSq (1 + z) = (1 + z.re) ^ 2 + z.im ^ 2 := by
    simp [Complex.normSq, pow_two]
  have hformula : (discToRight z).re =
      (1 - (z.re ^ 2 + z.im ^ 2)) / ((1 + z.re) ^ 2 + z.im ^ 2) := by
    rw [discToRight, Complex.div_re]
    simp only [Complex.one_re, Complex.sub_re, Complex.one_im, Complex.sub_im,
      Complex.add_re, Complex.add_im, zero_sub, zero_add]
    rw [hnormSq]
    field_simp [ne_of_gt hden]
    ring
  rw [hformula]
  exact div_pos (by linarith) hden

end

end EremenkoLyubichConstant
