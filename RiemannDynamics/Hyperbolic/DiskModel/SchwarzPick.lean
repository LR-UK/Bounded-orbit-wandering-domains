/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Hyperbolic.DiskModel.DiskMetric
import RiemannDynamics.Hyperbolic.DiskModel.MobiusDisk
import Mathlib.Analysis.Complex.Schwarz

/-!
# Schwarz–Pick inequality on the unit disk

A holomorphic self-map of the open unit disk `𝔻 = Metric.ball (0 : ℂ) 1`
is non-expansive with respect to the Poincaré hyperbolic distance defined
in `DiskMetric.lean`. The proof reduces — via the Möbius automorphisms
of `𝔻` from `MobiusDisk.lean` — to the centered Schwarz lemma already
available in Mathlib as `Complex.norm_le_norm_of_mapsTo_ball`.

We first prove the **Möbius form** (`schwarzPick_pseudo`):
`‖mobiusDisk (f w) (f z)‖ ≤ ‖mobiusDisk w z‖`. The full hyperbolic
inequality follows by translation through the algebraic identity
`‖mobiusDisk w z‖ / √(1 − ‖mobiusDisk w z‖²)
   = ‖z − w‖ / √((1−‖z‖²)(1−‖w‖²))`.
-/

namespace RiemannDynamics

open Complex Real Metric Set

/-- **Schwarz–Pick (Möbius form).** For a holomorphic self-map `f : 𝔻 → 𝔻`
the pseudohyperbolic norm `‖mobiusDisk w z‖ = ‖z − w‖ / ‖1 − conj(w) · z‖`
is non-expansive. -/
theorem schwarzPick_pseudo {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hf : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    ‖mobiusDisk (f w) (f z)‖ ≤ ‖mobiusDisk w z‖ := by
  have hfz : f z ∈ ball (0 : ℂ) 1 := hf hz
  have hfw : f w ∈ ball (0 : ℂ) 1 := hf hw
  have hnegw : -w ∈ ball (0 : ℂ) 1 := by
    have hw1 : ‖w‖ < 1 := by rwa [mem_ball, dist_zero_right] at hw
    rw [mem_ball, dist_zero_right, norm_neg]; exact hw1
  -- The auxiliary function g(ζ) = mobiusDisk (f w) (f (mobiusDisk (-w) ζ)).
  set g : ℂ → ℂ := fun ζ => mobiusDisk (f w) (f (mobiusDisk (-w) ζ)) with hg_def
  -- g sends 0 to 0.
  have hg0 : g 0 = 0 := by
    change mobiusDisk (f w) (f (mobiusDisk (-w) 0)) = 0
    rw [mobiusDisk_neg_apply_zero]; exact mobiusDisk_self (f w)
  -- mobiusDisk (-w) maps 𝔻 → 𝔻 (with parameter `-w` in 𝔻 too).
  have hMnegw_maps : MapsTo (mobiusDisk (-w)) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    fun ζ hζ => mobiusDisk_mapsTo hζ hnegw
  -- mobiusDisk (f w) maps 𝔻 → 𝔻.
  have hMfw_maps : MapsTo (mobiusDisk (f w)) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    fun ζ hζ => mobiusDisk_mapsTo hζ hfw
  -- g maps 𝔻 → 𝔻.
  have hg_maps : MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro ζ hζ
    change mobiusDisk (f w) (f (mobiusDisk (-w) ζ)) ∈ ball (0 : ℂ) 1
    exact hMfw_maps (hf (hMnegw_maps hζ))
  -- g maps 𝔻 → closedBall 0 1.
  have hg_maps_cl : MapsTo g (ball (0 : ℂ) 1) (closedBall (0 : ℂ) 1) :=
    fun ζ hζ => Metric.ball_subset_closedBall (hg_maps hζ)
  -- g is holomorphic on 𝔻.
  have hg_diff : DifferentiableOn ℂ g (ball (0 : ℂ) 1) := by
    have h1 : DifferentiableOn ℂ (mobiusDisk (-w)) (ball (0 : ℂ) 1) :=
      mobiusDisk_differentiableOn hnegw
    have h2 : DifferentiableOn ℂ (f ∘ mobiusDisk (-w)) (ball (0 : ℂ) 1) :=
      hd.comp h1 hMnegw_maps
    have h3 : DifferentiableOn ℂ (mobiusDisk (f w)) (ball (0 : ℂ) 1) :=
      mobiusDisk_differentiableOn hfw
    have h4 : MapsTo (f ∘ mobiusDisk (-w)) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
      fun ζ hζ => hf (hMnegw_maps hζ)
    exact h3.comp h2 h4
  -- Apply the centered Schwarz lemma to g.
  have hMwz : mobiusDisk w z ∈ ball (0 : ℂ) 1 := mobiusDisk_mapsTo hz hw
  have hMwz_norm : ‖mobiusDisk w z‖ < 1 := by
    rwa [mem_ball, dist_zero_right] at hMwz
  have h_centered_schwarz : ‖g (mobiusDisk w z)‖ ≤ ‖mobiusDisk w z‖ :=
    norm_le_norm_of_mapsTo_ball hg_diff hg_maps_cl hg0 hMwz_norm
  -- g (mobiusDisk w z) = mobiusDisk (f w) (f z).
  have hg_at_Mwz : g (mobiusDisk w z) = mobiusDisk (f w) (f z) := by
    change mobiusDisk (f w) (f (mobiusDisk (-w) (mobiusDisk w z))) = mobiusDisk (f w) (f z)
    rw [mobiusDisk_neg_mobiusDisk hz hw]
  rw [hg_at_Mwz] at h_centered_schwarz
  exact h_centered_schwarz

/-- **Schwarz–Pick inequality.** A holomorphic self-map of the open unit
disk is non-expansive with respect to the Poincaré hyperbolic distance. -/
theorem schwarzPick {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hf : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    hyperbolicDistDisk (f z) (f w) ≤ hyperbolicDistDisk z w := by
  have hfz : f z ∈ ball (0 : ℂ) 1 := hf hz
  have hfw : f w ∈ ball (0 : ℂ) 1 := hf hw
  -- Pseudo form: α := ‖M_{f w}(f z)‖ ≤ β := ‖M_w z‖ on `𝔻`.
  have h_pseudo : ‖mobiusDisk (f w) (f z)‖ ≤ ‖mobiusDisk w z‖ :=
    schwarzPick_pseudo hd hf hz hw
  -- Both ‖M_w z‖ and ‖M_{f w}(f z)‖ lie in `[0, 1)`.
  have hα_lt : ‖mobiusDisk (f w) (f z)‖ < 1 := by
    have := mobiusDisk_mapsTo hfz hfw
    rwa [mem_ball, dist_zero_right] at this
  have hβ_lt : ‖mobiusDisk w z‖ < 1 := by
    have := mobiusDisk_mapsTo hz hw
    rwa [mem_ball, dist_zero_right] at this
  -- Translation through `mobiusDisk_norm_div_eq`.
  have h_lhs := mobiusDisk_norm_div_eq hfz hfw
  have h_rhs := mobiusDisk_norm_div_eq hz hw
  -- Monotonicity of `x ↦ x / √(1 − x²)` on `[0, 1)`: from `α ≤ β` with
  -- both in `[0, 1)` deduce `α/√(1−α²) ≤ β/√(1−β²)`.
  have h_phi_mono : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < 1 →
      a / Real.sqrt (1 - a ^ 2) ≤ b / Real.sqrt (1 - b ^ 2) := by
    intro a b ha hab hb1
    have hab_nn : 0 ≤ b := le_trans ha hab
    have ha_sq : 0 ≤ a ^ 2 := sq_nonneg _
    have hb_sq_lt : b ^ 2 < 1 := by nlinarith
    have ha_sq_le : a ^ 2 ≤ b ^ 2 := by nlinarith
    have h_one_sub_b : 0 < 1 - b ^ 2 := by linarith
    have h_one_sub_a : 0 ≤ 1 - a ^ 2 := by linarith [le_trans ha_sq_le hb_sq_lt.le]
    have hsqrt_b : 0 < Real.sqrt (1 - b ^ 2) := Real.sqrt_pos.mpr h_one_sub_b
    by_cases ha0 : a = 0
    · subst ha0
      have : (0 : ℝ) / Real.sqrt (1 - (0 : ℝ) ^ 2) = 0 := by
        rw [zero_div]
      rw [this]
      positivity
    have ha_pos : 0 < a := ha.lt_of_ne (Ne.symm ha0)
    have h_one_sub_a_pos : 0 < 1 - a ^ 2 := by
      have : a ^ 2 < 1 := lt_of_le_of_lt ha_sq_le hb_sq_lt
      linarith
    have hsqrt_a : 0 < Real.sqrt (1 - a ^ 2) := Real.sqrt_pos.mpr h_one_sub_a_pos
    rw [div_le_div_iff₀ hsqrt_a hsqrt_b]
    -- Goal: a * √(1 − b²) ≤ b * √(1 − a²)
    have key_sq : (a * Real.sqrt (1 - b ^ 2)) ^ 2 ≤ (b * Real.sqrt (1 - a ^ 2)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt h_one_sub_b.le, Real.sq_sqrt h_one_sub_a]
      nlinarith
    have lhs_nn : 0 ≤ a * Real.sqrt (1 - b ^ 2) := mul_nonneg ha hsqrt_b.le
    have rhs_nn : 0 ≤ b * Real.sqrt (1 - a ^ 2) := mul_nonneg hab_nn hsqrt_a.le
    have := Real.sqrt_le_sqrt key_sq
    rwa [Real.sqrt_sq lhs_nn, Real.sqrt_sq rhs_nn] at this
  -- Apply monotonicity to get the inequality in the explicit formula form.
  have h_phi : ‖mobiusDisk (f w) (f z)‖ / Real.sqrt (1 - ‖mobiusDisk (f w) (f z)‖ ^ 2)
             ≤ ‖mobiusDisk w z‖ / Real.sqrt (1 - ‖mobiusDisk w z‖ ^ 2) :=
    h_phi_mono (norm_nonneg _) h_pseudo hβ_lt
  -- Substitute through h_lhs, h_rhs to convert to the hyperbolicDistDisk formula.
  rw [h_lhs, h_rhs] at h_phi
  -- Apply arsinh monotonicity, multiply by 2.
  unfold hyperbolicDistDisk
  have h_arsinh : Real.arsinh
        (‖f z - f w‖ / Real.sqrt ((1 - ‖f z‖ ^ 2) * (1 - ‖f w‖ ^ 2)))
      ≤ Real.arsinh
        (‖z - w‖ / Real.sqrt ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2))) :=
    Real.arsinh_le_arsinh.mpr h_phi
  linarith

end RiemannDynamics
