module

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Topology.MetricSpace.Defs

@[expose] public section

/-!
# Poincaré hyperbolic metric on the unit disk

The Poincaré hyperbolic distance on the open unit disk
`𝔻 := Metric.ball (0 : ℂ) 1`, given by the formula

  `d_𝔻(z,w) = 2 · arsinh ( |z − w| / √((1 − |z|²)(1 − |w|²)) )`.

The closed formula is used directly; outside `𝔻` the formula returns the
"junk" value `0` because of Mathlib's convention that
`Real.sqrt` of a negative number is `0`.

This file proves the distance axioms, including the triangle inequality,
by comparison with the upper half-plane model.

`SchwarzPick.lean` uses this metric to state the Schwarz–Pick
inequality for holomorphic self-maps of `𝔻`.
-/

namespace RiemannDynamics

open Complex Real Metric

/-- The Poincaré hyperbolic distance on the open unit disk
`𝔻 = Metric.ball (0 : ℂ) 1`. -/
noncomputable def hyperbolicDistDisk (z w : ℂ) : ℝ :=
  2 * Real.arsinh (‖z - w‖ / Real.sqrt ((1 - ‖z‖^2) * (1 - ‖w‖^2)))

/-- The hyperbolic distance from a point to itself is zero. -/
theorem hyperbolicDistDisk_self (z : ℂ) : hyperbolicDistDisk z z = 0 := by
  simp [hyperbolicDistDisk, Real.arsinh_zero]

/-- The hyperbolic distance is symmetric. -/
theorem hyperbolicDistDisk_comm (z w : ℂ) :
    hyperbolicDistDisk z w = hyperbolicDistDisk w z := by
  unfold hyperbolicDistDisk
  rw [norm_sub_rev z w, mul_comm (1 - ‖w‖^2) (1 - ‖z‖^2)]

/-- The hyperbolic distance is non-negative. -/
theorem hyperbolicDistDisk_nonneg (z w : ℂ) : 0 ≤ hyperbolicDistDisk z w := by
  unfold hyperbolicDistDisk
  have h1 : 0 ≤ ‖z - w‖ / Real.sqrt ((1 - ‖z‖^2) * (1 - ‖w‖^2)) := by positivity
  have h2 : 0 ≤ Real.arsinh (‖z - w‖ / Real.sqrt ((1 - ‖z‖^2) * (1 - ‖w‖^2))) :=
    Real.arsinh_nonneg_iff.mpr h1
  linarith

/-- On the unit disk, the hyperbolic distance vanishes only on the diagonal. -/
theorem hyperbolicDistDisk_eq_zero_iff {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    hyperbolicDistDisk z w = 0 ↔ z = w := by
  have hz' : ‖z‖ < 1 := by rwa [mem_ball, dist_zero_right] at hz
  have hw' : ‖w‖ < 1 := by rwa [mem_ball, dist_zero_right] at hw
  have hz2 : 0 < 1 - ‖z‖^2 := by nlinarith [norm_nonneg z]
  have hw2 : 0 < 1 - ‖w‖^2 := by nlinarith [norm_nonneg w]
  have hprod : 0 < (1 - ‖z‖^2) * (1 - ‖w‖^2) := mul_pos hz2 hw2
  have hsqrt : 0 < Real.sqrt ((1 - ‖z‖^2) * (1 - ‖w‖^2)) := Real.sqrt_pos.mpr hprod
  refine ⟨fun h => ?_, fun h => h ▸ hyperbolicDistDisk_self z⟩
  unfold hyperbolicDistDisk at h
  have harsh : Real.arsinh
      (‖z - w‖ / Real.sqrt ((1 - ‖z‖^2) * (1 - ‖w‖^2))) = 0 := by linarith
  have hdiv : ‖z - w‖ / Real.sqrt ((1 - ‖z‖^2) * (1 - ‖w‖^2)) = 0 :=
    Real.arsinh_eq_zero_iff.mp harsh
  have hnum : ‖z - w‖ = 0 :=
    (div_eq_zero_iff.mp hdiv).resolve_right hsqrt.ne'
  exact sub_eq_zero.mp (norm_eq_zero.mp hnum)

/-! ## Cayley transform `𝔻 → ℍ` and the triangle inequality

The triangle inequality for `hyperbolicDistDisk` is obtained by pulling
back Mathlib's `MetricSpace UpperHalfPlane` structure through the Cayley
transform `C(z) = i · (1 + z) / (1 − z)`, which is a hyperbolic isometry
of the unit disk onto the upper half-plane.
-/

/-- The Cayley transform `𝔻 → ℍ` on `ℂ`: `z ↦ i · (1 + z) / (1 − z)`.
Defined on all of `ℂ`; restricted to `𝔻 = ball (0 : ℂ) 1` it lands in the
open upper half-plane. -/
noncomputable def cayleyToHalfPlane (z : ℂ) : ℂ := Complex.I * (1 + z) / (1 - z)

/-- For `z ∈ 𝔻`, `1 − z ≠ 0`. -/
theorem one_sub_ne_zero_of_mem_ball {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    (1 : ℂ) - z ≠ 0 := by
  intro heq
  have h_eq : z = 1 := by linear_combination -heq
  rw [mem_ball, dist_zero_right, h_eq] at hz
  norm_num at hz

/-- Imaginary part of the Cayley image:
`Im(C(z)) = (1 − ‖z‖²) / ‖1 − z‖²` (holds unconditionally; the division by
zero at `z = 1` is a Lean junk value on both sides). -/
theorem cayleyToHalfPlane_im (z : ℂ) :
    (cayleyToHalfPlane z).im = (1 - ‖z‖ ^ 2) / ‖(1 : ℂ) - z‖ ^ 2 := by
  rw [show ‖z‖ ^ 2 = Complex.normSq z from (Complex.normSq_eq_norm_sq z).symm,
      show ‖(1 : ℂ) - z‖ ^ 2 = Complex.normSq ((1 : ℂ) - z) from
        (Complex.normSq_eq_norm_sq _).symm]
  unfold cayleyToHalfPlane
  rw [Complex.div_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
             Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
             Complex.sub_re, Complex.sub_im, Complex.normSq_apply]
  ring

/-- For `z ∈ 𝔻`, the Cayley image has positive imaginary part. -/
theorem cayleyToHalfPlane_im_pos {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    0 < (cayleyToHalfPlane z).im := by
  rw [cayleyToHalfPlane_im z]
  have hz1 : ‖z‖ < 1 := by rwa [mem_ball, dist_zero_right] at hz
  have hone_minus_pos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have h1mz_ne : (1 : ℂ) - z ≠ 0 := one_sub_ne_zero_of_mem_ball hz
  have h_norm_pos : 0 < ‖(1 : ℂ) - z‖ := norm_pos_iff.mpr h1mz_ne
  positivity

/-- Package `z ∈ 𝔻` as an element of `ℍ = UpperHalfPlane` via the Cayley
transform. -/
noncomputable def diskToHalfPlane {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    UpperHalfPlane :=
  ⟨cayleyToHalfPlane z, cayleyToHalfPlane_im_pos hz⟩

/-- The inverse Cayley transform `ℍ → 𝔻`: `τ ↦ (τ − i) / (τ + i)`. -/
noncomputable def halfPlaneToCayley (τ : ℂ) : ℂ := (τ - Complex.I) / (τ + Complex.I)

/-- For `τ ∈ ℍ` (i.e. `0 < τ.im`), `τ + i ≠ 0`. -/
theorem add_I_ne_zero_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) :
    τ + Complex.I ≠ 0 := by
  intro h
  have h_im : (τ + Complex.I).im = 0 := by rw [h]; simp
  simp [Complex.add_im, Complex.I_im] at h_im
  linarith

/-- `halfPlaneToCayley` is a left inverse of `cayleyToHalfPlane` on `ℍ`. -/
theorem cayleyToHalfPlane_halfPlaneToCayley {τ : ℂ} (hτ : 0 < τ.im) :
    cayleyToHalfPlane (halfPlaneToCayley τ) = τ := by
  unfold cayleyToHalfPlane halfPlaneToCayley
  have h_add_ne : τ + Complex.I ≠ 0 := add_I_ne_zero_of_im_pos hτ
  field_simp
  ring

/-- `cayleyToHalfPlane` is a left inverse of `halfPlaneToCayley` on `𝔻`. -/
theorem halfPlaneToCayley_cayleyToHalfPlane {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    halfPlaneToCayley (cayleyToHalfPlane z) = z := by
  unfold cayleyToHalfPlane halfPlaneToCayley
  have h_ne : (1 - z) ≠ 0 := one_sub_ne_zero_of_mem_ball hz
  field_simp
  ring

/-- For `τ ∈ ℍ`, `‖halfPlaneToCayley τ‖ < 1`, i.e., the image lands in `𝔻`. -/
theorem halfPlaneToCayley_mem_ball {τ : ℂ} (hτ : 0 < τ.im) :
    halfPlaneToCayley τ ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball, dist_zero_right]
  unfold halfPlaneToCayley
  have h_add_ne : τ + Complex.I ≠ 0 := add_I_ne_zero_of_im_pos hτ
  rw [norm_div]
  rw [div_lt_one (by positivity)]
  -- ‖τ − i‖² = (τ.re)² + (τ.im − 1)²; ‖τ + i‖² = (τ.re)² + (τ.im + 1)².
  -- For τ.im > 0: (τ.im + 1)² > (τ.im − 1)², so ‖τ + i‖ > ‖τ − i‖.
  have h_sq_lt : ‖τ - Complex.I‖^2 < ‖τ + Complex.I‖^2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
          Complex.add_im, Complex.I_re, Complex.I_im]
    nlinarith
  have h_nonneg_left : 0 ≤ ‖τ - Complex.I‖ := norm_nonneg _
  have h_nonneg_right : 0 ≤ ‖τ + Complex.I‖ := norm_nonneg _
  exact lt_of_pow_lt_pow_left₀ 2 h_nonneg_right h_sq_lt

/-- **Cayley image of the disk equals `ℍ`.** This is the bijection
between `𝔻` and `ℍ` at the level of underlying sets in `ℂ`. -/
theorem cayleyToHalfPlane_image_ball :
    cayleyToHalfPlane '' ball (0 : ℂ) 1 = { τ : ℂ | 0 < τ.im } := by
  ext τ
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact cayleyToHalfPlane_im_pos hz
  · intro hτ_pos
    refine ⟨halfPlaneToCayley τ, halfPlaneToCayley_mem_ball hτ_pos, ?_⟩
    exact cayleyToHalfPlane_halfPlaneToCayley hτ_pos

/-- Algebraic difference of Cayley images: `C(z) − C(w) = 2i (z − w) / ((1 − z)(1 − w))`. -/
theorem cayleyToHalfPlane_sub {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    cayleyToHalfPlane z - cayleyToHalfPlane w
      = 2 * Complex.I * (z - w) / ((1 - z) * (1 - w)) := by
  have h1mz : (1 : ℂ) - z ≠ 0 := one_sub_ne_zero_of_mem_ball hz
  have h1mw : (1 : ℂ) - w ≠ 0 := one_sub_ne_zero_of_mem_ball hw
  unfold cayleyToHalfPlane
  field_simp
  ring

/-- Norm of the difference of Cayley images:
`‖C(z) − C(w)‖ = 2 ‖z − w‖ / (‖1 − z‖ · ‖1 − w‖)`. -/
theorem cayleyToHalfPlane_sub_norm {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    ‖cayleyToHalfPlane z - cayleyToHalfPlane w‖
      = 2 * ‖z - w‖ / (‖(1 : ℂ) - z‖ * ‖(1 : ℂ) - w‖) := by
  rw [cayleyToHalfPlane_sub hz hw, norm_div, norm_mul, norm_mul, norm_mul,
      Complex.norm_I, mul_one,
      show ‖(2 : ℂ)‖ = 2 from by norm_num]

/-- The Cayley transform pulls back `UpperHalfPlane.dist` to
`hyperbolicDistDisk`. -/
theorem hyperbolicDistDisk_eq_upperHalfPlane_dist {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    hyperbolicDistDisk z w = dist (diskToHalfPlane hz) (diskToHalfPlane hw) := by
  rw [UpperHalfPlane.dist_eq]
  unfold hyperbolicDistDisk
  congr 1
  congr 1
  -- Unwrap the UpperHalfPlane coercions on the right-hand side.
  have h_coe_z : ((diskToHalfPlane hz : UpperHalfPlane) : ℂ) = cayleyToHalfPlane z := rfl
  have h_coe_w : ((diskToHalfPlane hw : UpperHalfPlane) : ℂ) = cayleyToHalfPlane w := rfl
  have h_im_z : (diskToHalfPlane hz).im = (cayleyToHalfPlane z).im := rfl
  have h_im_w : (diskToHalfPlane hw).im = (cayleyToHalfPlane w).im := rfl
  rw [Complex.dist_eq, h_coe_z, h_coe_w, h_im_z, h_im_w]
  rw [cayleyToHalfPlane_sub_norm hz hw, cayleyToHalfPlane_im z, cayleyToHalfPlane_im w]
  -- Positivity setup.
  have hz1 : ‖z‖ < 1 := by rwa [mem_ball, dist_zero_right] at hz
  have hw1 : ‖w‖ < 1 := by rwa [mem_ball, dist_zero_right] at hw
  have hz2 : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hw2 : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have h1mz_pos : 0 < ‖(1 : ℂ) - z‖ := norm_pos_iff.mpr (one_sub_ne_zero_of_mem_ball hz)
  have h1mw_pos : 0 < ‖(1 : ℂ) - w‖ := norm_pos_iff.mpr (one_sub_ne_zero_of_mem_ball hw)
  have hP : 0 < (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := mul_pos hz2 hw2
  have hP_sqrt_pos : 0 < Real.sqrt ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) := Real.sqrt_pos.mpr hP
  -- Simplify the right-hand sqrt: √((1-‖z‖²)/‖1-z‖² · (1-‖w‖²)/‖1-w‖²)
  --   = √((1-‖z‖²)(1-‖w‖²)) / (‖1-z‖ · ‖1-w‖).
  have h_sqrt_eq : Real.sqrt ((1 - ‖z‖ ^ 2) / ‖(1 : ℂ) - z‖ ^ 2
                              * ((1 - ‖w‖ ^ 2) / ‖(1 : ℂ) - w‖ ^ 2))
                 = Real.sqrt ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2))
                    / (‖(1 : ℂ) - z‖ * ‖(1 : ℂ) - w‖) := by
    rw [show ((1 - ‖z‖ ^ 2) / ‖(1 : ℂ) - z‖ ^ 2 * ((1 - ‖w‖ ^ 2) / ‖(1 : ℂ) - w‖ ^ 2))
          = ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2))
              / (‖(1 : ℂ) - z‖ ^ 2 * ‖(1 : ℂ) - w‖ ^ 2) from by ring]
    rw [Real.sqrt_div hP.le,
        show ‖(1 : ℂ) - z‖ ^ 2 * ‖(1 : ℂ) - w‖ ^ 2
            = (‖(1 : ℂ) - z‖ * ‖(1 : ℂ) - w‖) ^ 2 from by ring,
        Real.sqrt_sq (by positivity)]
  rw [h_sqrt_eq]
  field_simp

/-- The triangle inequality for the Poincaré hyperbolic distance on `𝔻`.
Proof via the Cayley transform: the metric pulls back from
`UpperHalfPlane.dist`, which carries `dist_triangle` from Mathlib's
`MetricSpace ℍ` instance. -/
theorem hyperbolicDistDisk_triangle {z w v : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) (hv : v ∈ ball (0 : ℂ) 1) :
    hyperbolicDistDisk z v ≤ hyperbolicDistDisk z w + hyperbolicDistDisk w v := by
  rw [hyperbolicDistDisk_eq_upperHalfPlane_dist hz hv,
      hyperbolicDistDisk_eq_upperHalfPlane_dist hz hw,
      hyperbolicDistDisk_eq_upperHalfPlane_dist hw hv]
  exact dist_triangle _ _ _

end RiemannDynamics
