/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.CuspDensityBounds

/-! # A logarithmic derivative bound on an exterior-valued disc

This is the upper estimate in the Eremenko--Lyubich no-escape argument.
It follows from the zero-free disc estimate by inversion.
-/

open Set Metric Function

namespace AreaDeficit

theorem logarithmic_derivative_bound_of_exterior
    {g : ℂ → ℂ} {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
    (hg : DifferentiableOn ℂ g (ball 0 r))
    (hgm : ∀ w ∈ ball 0 r, M < ‖g w‖) :
    ‖deriv g 0‖ / ‖g 0‖ ≤
      (4 / r) * (1 + Real.log ‖g 0‖ - Real.log M) := by
  have h0 : (0 : ℂ) ∈ ball 0 r := mem_ball_self hr
  have hne : ∀ w ∈ ball 0 r, g w ≠ 0 := fun w hw =>
    norm_pos_iff.mp (hM.trans (hgm w hw))
  have hn : 0 < ‖g 0‖ := hM.trans (hgm 0 h0)
  have hi := norm_deriv_le_of_zero_free_bounded hr (hg.inv hne)
    (fun w hw => inv_ne_zero (hne w hw)) (B := M⁻¹) (by
      intro w hw
      change ‖(g w)⁻¹‖ ≤ M⁻¹
      rw [norm_inv]
      exact inv_le_inv₀ (hM.trans (hgm w hw)) hM |>.mpr (hgm w hw).le)
  have hder : deriv (fun w => (g w)⁻¹) 0 = -deriv g 0 / (g 0)^2 :=
    ((hg.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt.inv (hne 0 h0)).deriv
  change ‖deriv (fun w => (g w)⁻¹) 0‖ ≤ 4 * ‖(g 0)⁻¹‖ *
    (1 + Real.log M⁻¹ - Real.log ‖(g 0)⁻¹‖) / r at hi
  rw [hder, norm_div, norm_neg, norm_pow, norm_inv, Real.log_inv, Real.log_inv] at hi
  have ht := mul_le_mul_of_nonneg_right hi hn.le
  convert ht using 1 <;> (field_simp; ring)

/-- A positive sequence that at least doubles cannot have a fixed upper bound. -/
theorem not_bounded_of_doubling {q : ℕ → ℝ} (h0 : 0 < q 0)
    (hstep : ∀ n, 2 * q n ≤ q (n + 1)) (C : ℝ) : ¬ ∀ n, q n ≤ C := by
  intro hb
  have hl : ∀ n : ℕ, ((n : ℝ) + 1) * q 0 ≤ q n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      have hs := hstep n
      push_cast
      nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt (C / q 0)
  have hlt : C < (n : ℝ) * q 0 := (div_lt_iff₀ h0).mp hn
  have := hl n
  have := hb n
  nlinarith

end AreaDeficit
