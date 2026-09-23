/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RiemannDynamics.Sphere.Basic

/-!
# The spherical (chordal) metric on `ℂ̂`

We equip the Riemann sphere `ℂ̂` with the chordal / Fubini–Study metric, defined
by `d(z, w) = 2|z - w| / (√(1 + |z|²) √(1 + |w|²))` for finite `z, w`, extended
to handle `∞` as the corresponding stereographic limit.

This metric is *topologically equivalent* to the one-point-compactification
topology already on `ℂ̂` (Mathlib's `OnePoint ℂ` instance), but its metric form
is what the dynamics line uses for spherical-metric normal families and for
Julia/Fatou set hyperbolicity.

## Main definitions

* `chordalDist`, `chordalDistInfty` — the chordal distance between two finite
  points, and from a finite point to `∞`.
* `sphericalDist` — the chordal / Fubini–Study metric on `ℂ̂`.
* `stereoEmbed` — the inverse stereographic embedding `ℂ̂ → S² ⊂ ℝ³`.

## Main results

* `dist_stereoEmbed_eq_sphericalDist` — `sphericalDist` equals the Euclidean
  distance between the stereographic images.
* `sphericalDist_comm`, `sphericalDist_nonneg`, `sphericalDist_eq_zero_iff`,
  `sphericalDist_triangle` — the metric-space axioms for `sphericalDist`.
* `sphericalDist_induces_topology` — the metric topology is the one-point
  compactification topology already on `ℂ̂`.

## Implementation notes

We do not promote `sphericalDist` to a `MetricSpace` instance here: the instance
is added where it is first consumed, to avoid a diamond with the existing
`OnePoint ℂ` topology.
-/

open OnePoint Real

namespace RiemannDynamics

/-- The chordal distance between two finite points of `ℂ`, viewed via
stereographic projection of the unit sphere `S² ⊂ ℝ³` onto `ℂ`. -/
noncomputable def chordalDist (z w : ℂ) : ℝ :=
  2 * ‖z - w‖ / (Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2))

/-- The chordal distance from a finite point `z` to `∞`. -/
noncomputable def chordalDistInfty (z : ℂ) : ℝ :=
  2 / Real.sqrt (1 + ‖z‖ ^ 2)

/-- The chordal / Fubini–Study metric on `ℂ̂`. We define it by cases on the
two points; at finite × finite it is `chordalDist`, at finite × ∞ it is
`chordalDistInfty`, and at ∞ × ∞ it is `0`. -/
noncomputable def sphericalDist : ℂ̂ → ℂ̂ → ℝ := fun z w =>
  match z, w with
  | OnePoint.some a, OnePoint.some b => chordalDist a b
  | OnePoint.some a, ∞ => chordalDistInfty a
  | ∞, OnePoint.some b => chordalDistInfty b
  | ∞, ∞ => 0

/-- The inverse stereographic embedding `ℂ̂ → S² ⊂ ℝ³`. Finite `w ∈ ℂ` maps to
the point of the unit sphere `S² ⊂ ℝ³` whose stereographic projection from the
north pole is `w`; the point `∞ ∈ ℂ̂` maps to the north pole itself. The chordal
distance on `ℂ̂` equals the Euclidean (L²) distance between the images. -/
noncomputable def stereoEmbed : ℂ̂ → EuclideanSpace ℝ (Fin 3) := fun z =>
  (EuclideanSpace.equiv (Fin 3) ℝ).symm <|
    match z with
    | OnePoint.some w =>
        ![2 * w.re / (1 + ‖w‖ ^ 2),
          2 * w.im / (1 + ‖w‖ ^ 2),
          (‖w‖ ^ 2 - 1) / (1 + ‖w‖ ^ 2)]
    | ∞ => ![0, 0, 1]

/-! ## Metric-space axioms

These three theorems together state that `sphericalDist` is a metric, and the
metric topology it induces is the one-point compactification topology already
on `ℂ̂`. We do not yet promote this to a `MetricSpace` instance — instances
on `ℂ̂` are added where they are first consumed. -/

/-- The defining identity: the chordal metric is the pullback of the
Euclidean (`L²`) metric on `S² ⊂ ℝ³` under the inverse stereographic
embedding. This is the geometric content from which symmetry, the triangle
inequality, and the upper bound by `2` all follow. -/
theorem dist_stereoEmbed_eq_sphericalDist (z w : ℂ̂) :
    dist (stereoEmbed z) (stereoEmbed w) = sphericalDist z w := by
  -- Common preparation: helpers on positivity of 1 + ‖·‖²
  have norm_sq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  match z, w with
  | ∞, ∞ =>
      simp only [stereoEmbed, sphericalDist, dist_self]
  | OnePoint.some w, ∞ =>
      have hpos : (0 : ℝ) < 1 + ‖w‖ ^ 2 := by positivity
      have hsqrt_pos : (0 : ℝ) < Real.sqrt (1 + ‖w‖ ^ 2) := Real.sqrt_pos.mpr hpos
      -- both sides nonneg, compare squares
      have lhs_nn : 0 ≤ dist (stereoEmbed (↑w : ℂ̂)) (stereoEmbed ∞) := dist_nonneg
      have rhs_nn : 0 ≤ chordalDistInfty w := by unfold chordalDistInfty; positivity
      apply (sq_eq_sq₀ lhs_nn rhs_nn).mp
      show (dist (stereoEmbed (↑w : ℂ̂)) (stereoEmbed ∞)) ^ 2
        = (chordalDistInfty w) ^ 2
      rw [EuclideanSpace.dist_sq_eq]
      simp only [stereoEmbed, Fin.sum_univ_three, Real.dist_eq, sq_abs]
      have h0 : ((EuclideanSpace.equiv (Fin 3) ℝ).symm
          ![2 * w.re / (1 + ‖w‖ ^ 2), 2 * w.im / (1 + ‖w‖ ^ 2),
            (‖w‖ ^ 2 - 1) / (1 + ‖w‖ ^ 2)]) 0 = 2 * w.re / (1 + ‖w‖ ^ 2) := rfl
      have h1 : ((EuclideanSpace.equiv (Fin 3) ℝ).symm
          ![2 * w.re / (1 + ‖w‖ ^ 2), 2 * w.im / (1 + ‖w‖ ^ 2),
            (‖w‖ ^ 2 - 1) / (1 + ‖w‖ ^ 2)]) 1 = 2 * w.im / (1 + ‖w‖ ^ 2) := rfl
      have h2 : ((EuclideanSpace.equiv (Fin 3) ℝ).symm
          ![2 * w.re / (1 + ‖w‖ ^ 2), 2 * w.im / (1 + ‖w‖ ^ 2),
            (‖w‖ ^ 2 - 1) / (1 + ‖w‖ ^ 2)]) 2 = (‖w‖ ^ 2 - 1) / (1 + ‖w‖ ^ 2) := rfl
      have h0' : ((EuclideanSpace.equiv (Fin 3) ℝ).symm
          ![(0 : ℝ), 0, 1]) 0 = 0 := rfl
      have h1' : ((EuclideanSpace.equiv (Fin 3) ℝ).symm
          ![(0 : ℝ), 0, 1]) 1 = 0 := rfl
      have h2' : ((EuclideanSpace.equiv (Fin 3) ℝ).symm
          ![(0 : ℝ), 0, 1]) 2 = 1 := rfl
      rw [h0, h1, h2, h0', h1', h2']
      have hns : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := norm_sq w
      unfold chordalDistInfty
      rw [div_pow, Real.sq_sqrt hpos.le]
      field_simp
      nlinarith [sq_nonneg w.re, sq_nonneg w.im, hns]
  | ∞, OnePoint.some w =>
      have hpos : (0 : ℝ) < 1 + ‖w‖ ^ 2 := by positivity
      have lhs_nn : 0 ≤ dist (stereoEmbed ∞) (stereoEmbed (↑w : ℂ̂)) := dist_nonneg
      have rhs_nn : 0 ≤ chordalDistInfty w := by unfold chordalDistInfty; positivity
      apply (sq_eq_sq₀ lhs_nn rhs_nn).mp
      show (dist (stereoEmbed ∞) (stereoEmbed (↑w : ℂ̂))) ^ 2
        = (chordalDistInfty w) ^ 2
      rw [EuclideanSpace.dist_sq_eq]
      simp only [stereoEmbed, Fin.sum_univ_three, Real.dist_eq, sq_abs]
      have h0 : ((EuclideanSpace.equiv (Fin 3) ℝ).symm
          ![2 * w.re / (1 + ‖w‖ ^ 2), 2 * w.im / (1 + ‖w‖ ^ 2),
            (‖w‖ ^ 2 - 1) / (1 + ‖w‖ ^ 2)]) 0 = 2 * w.re / (1 + ‖w‖ ^ 2) := rfl
      have h1 : ((EuclideanSpace.equiv (Fin 3) ℝ).symm
          ![2 * w.re / (1 + ‖w‖ ^ 2), 2 * w.im / (1 + ‖w‖ ^ 2),
            (‖w‖ ^ 2 - 1) / (1 + ‖w‖ ^ 2)]) 1 = 2 * w.im / (1 + ‖w‖ ^ 2) := rfl
      have h2 : ((EuclideanSpace.equiv (Fin 3) ℝ).symm
          ![2 * w.re / (1 + ‖w‖ ^ 2), 2 * w.im / (1 + ‖w‖ ^ 2),
            (‖w‖ ^ 2 - 1) / (1 + ‖w‖ ^ 2)]) 2 = (‖w‖ ^ 2 - 1) / (1 + ‖w‖ ^ 2) := rfl
      have h0' : ((EuclideanSpace.equiv (Fin 3) ℝ).symm
          ![(0 : ℝ), 0, 1]) 0 = 0 := rfl
      have h1' : ((EuclideanSpace.equiv (Fin 3) ℝ).symm
          ![(0 : ℝ), 0, 1]) 1 = 0 := rfl
      have h2' : ((EuclideanSpace.equiv (Fin 3) ℝ).symm
          ![(0 : ℝ), 0, 1]) 2 = 1 := rfl
      rw [h0, h1, h2, h0', h1', h2']
      have hns : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := norm_sq w
      unfold chordalDistInfty
      rw [div_pow, Real.sq_sqrt hpos.le]
      field_simp
      nlinarith [sq_nonneg w.re, sq_nonneg w.im, hns]
  | OnePoint.some w₁, OnePoint.some w₂ =>
      have hpos₁ : (0 : ℝ) < 1 + ‖w₁‖ ^ 2 := by positivity
      have hpos₂ : (0 : ℝ) < 1 + ‖w₂‖ ^ 2 := by positivity
      have lhs_nn : 0 ≤ dist (stereoEmbed (↑w₁ : ℂ̂)) (stereoEmbed (↑w₂ : ℂ̂)) :=
        dist_nonneg
      have rhs_nn : 0 ≤ chordalDist w₁ w₂ := by unfold chordalDist; positivity
      apply (sq_eq_sq₀ lhs_nn rhs_nn).mp
      show (dist (stereoEmbed (↑w₁ : ℂ̂)) (stereoEmbed (↑w₂ : ℂ̂))) ^ 2
        = (chordalDist w₁ w₂) ^ 2
      rw [EuclideanSpace.dist_sq_eq]
      simp only [stereoEmbed, Fin.sum_univ_three, Real.dist_eq, sq_abs]
      have h0₁ : ((EuclideanSpace.equiv (Fin 3) ℝ).symm
          ![2 * w₁.re / (1 + ‖w₁‖ ^ 2), 2 * w₁.im / (1 + ‖w₁‖ ^ 2),
            (‖w₁‖ ^ 2 - 1) / (1 + ‖w₁‖ ^ 2)]) 0 = 2 * w₁.re / (1 + ‖w₁‖ ^ 2) := rfl
      have h1₁ : ((EuclideanSpace.equiv (Fin 3) ℝ).symm
          ![2 * w₁.re / (1 + ‖w₁‖ ^ 2), 2 * w₁.im / (1 + ‖w₁‖ ^ 2),
            (‖w₁‖ ^ 2 - 1) / (1 + ‖w₁‖ ^ 2)]) 1 = 2 * w₁.im / (1 + ‖w₁‖ ^ 2) := rfl
      have h2₁ : ((EuclideanSpace.equiv (Fin 3) ℝ).symm
          ![2 * w₁.re / (1 + ‖w₁‖ ^ 2), 2 * w₁.im / (1 + ‖w₁‖ ^ 2),
            (‖w₁‖ ^ 2 - 1) / (1 + ‖w₁‖ ^ 2)]) 2 = (‖w₁‖ ^ 2 - 1) / (1 + ‖w₁‖ ^ 2) := rfl
      have h0₂ : ((EuclideanSpace.equiv (Fin 3) ℝ).symm
          ![2 * w₂.re / (1 + ‖w₂‖ ^ 2), 2 * w₂.im / (1 + ‖w₂‖ ^ 2),
            (‖w₂‖ ^ 2 - 1) / (1 + ‖w₂‖ ^ 2)]) 0 = 2 * w₂.re / (1 + ‖w₂‖ ^ 2) := rfl
      have h1₂ : ((EuclideanSpace.equiv (Fin 3) ℝ).symm
          ![2 * w₂.re / (1 + ‖w₂‖ ^ 2), 2 * w₂.im / (1 + ‖w₂‖ ^ 2),
            (‖w₂‖ ^ 2 - 1) / (1 + ‖w₂‖ ^ 2)]) 1 = 2 * w₂.im / (1 + ‖w₂‖ ^ 2) := rfl
      have h2₂ : ((EuclideanSpace.equiv (Fin 3) ℝ).symm
          ![2 * w₂.re / (1 + ‖w₂‖ ^ 2), 2 * w₂.im / (1 + ‖w₂‖ ^ 2),
            (‖w₂‖ ^ 2 - 1) / (1 + ‖w₂‖ ^ 2)]) 2 = (‖w₂‖ ^ 2 - 1) / (1 + ‖w₂‖ ^ 2) := rfl
      rw [h0₁, h1₁, h2₁, h0₂, h1₂, h2₂]
      have hns₁ : ‖w₁‖ ^ 2 = w₁.re ^ 2 + w₁.im ^ 2 := norm_sq w₁
      have hns₂ : ‖w₂‖ ^ 2 = w₂.re ^ 2 + w₂.im ^ 2 := norm_sq w₂
      have hns_sub : ‖w₁ - w₂‖ ^ 2 = (w₁.re - w₂.re) ^ 2 + (w₁.im - w₂.im) ^ 2 := by
        have := norm_sq (w₁ - w₂); simpa [Complex.sub_re, Complex.sub_im] using this
      unfold chordalDist
      simp only [div_pow, mul_pow]
      rw [Real.sq_sqrt hpos₁.le, Real.sq_sqrt hpos₂.le]
      rw [hns₁, hns₂, hns_sub] at *
      field_simp
      ring

/-- The spherical distance is symmetric. -/
theorem sphericalDist_comm (z w : ℂ̂) : sphericalDist z w = sphericalDist w z := by
  match z, w with
  | OnePoint.some a, OnePoint.some b =>
      simp only [sphericalDist, chordalDist]
      rw [norm_sub_rev, mul_comm (Real.sqrt _)]
  | OnePoint.some _, ∞ => rfl
  | ∞, OnePoint.some _ => rfl
  | ∞, ∞ => rfl

/-- The spherical distance is non-negative. -/
theorem sphericalDist_nonneg (z w : ℂ̂) : 0 ≤ sphericalDist z w := by
  match z, w with
  | OnePoint.some a, OnePoint.some b =>
      simp only [sphericalDist, chordalDist]; positivity
  | OnePoint.some _, ∞ =>
      simp only [sphericalDist, chordalDistInfty]; positivity
  | ∞, OnePoint.some _ =>
      simp only [sphericalDist, chordalDistInfty]; positivity
  | ∞, ∞ => exact le_refl 0

/-- The spherical distance vanishes iff its two arguments coincide. -/
theorem sphericalDist_eq_zero_iff (z w : ℂ̂) :
    sphericalDist z w = 0 ↔ z = w := by
  match z, w with
  | OnePoint.some a, OnePoint.some b =>
      simp only [sphericalDist, chordalDist]
      have hpos : (0 : ℝ) < Real.sqrt (1 + ‖a‖ ^ 2) * Real.sqrt (1 + ‖b‖ ^ 2) :=
        mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr (by positivity))
      rw [div_eq_zero_iff]
      simp only [hpos.ne', or_false]
      constructor
      · intro h
        have : ‖a - b‖ = 0 := by linarith
        have hab : a - b = 0 := norm_eq_zero.mp this
        rw [show a = b from sub_eq_zero.mp hab]
      · intro h
        have hab : a = b := OnePoint.coe_eq_coe.mp h
        subst hab
        simp
  | OnePoint.some a, ∞ =>
      simp only [sphericalDist, chordalDistInfty]
      have hpos : (0 : ℝ) < Real.sqrt (1 + ‖a‖ ^ 2) :=
        Real.sqrt_pos.mpr (by positivity)
      rw [div_eq_zero_iff]
      simp only [hpos.ne', or_false]
      constructor
      · intro h
        exfalso; norm_num at h
      · intro h
        exact absurd h (OnePoint.coe_ne_infty a)
  | ∞, OnePoint.some b =>
      simp only [sphericalDist, chordalDistInfty]
      have hpos : (0 : ℝ) < Real.sqrt (1 + ‖b‖ ^ 2) :=
        Real.sqrt_pos.mpr (by positivity)
      rw [div_eq_zero_iff]
      simp only [hpos.ne', or_false]
      constructor
      · intro h
        exfalso; norm_num at h
      · intro h
        exact absurd h (OnePoint.infty_ne_coe b)
  | ∞, ∞ => exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- Triangle inequality for the spherical metric. -/
theorem sphericalDist_triangle (z w v : ℂ̂) :
    sphericalDist z v ≤ sphericalDist z w + sphericalDist w v := by
  rw [← dist_stereoEmbed_eq_sphericalDist z v,
      ← dist_stereoEmbed_eq_sphericalDist z w,
      ← dist_stereoEmbed_eq_sphericalDist w v]
  exact dist_triangle _ _ _

/-- The spherical metric is bounded by `2` (the diameter of the Riemann sphere
viewed as the unit sphere `S² ⊂ ℝ³` with chordal distance). -/
theorem sphericalDist_le_two (z w : ℂ̂) : sphericalDist z w ≤ 2 := by
  match z, w with
  | OnePoint.some a, OnePoint.some b =>
      simp only [sphericalDist, chordalDist]
      have hA : (0 : ℝ) < Real.sqrt (1 + ‖a‖ ^ 2) :=
        Real.sqrt_pos.mpr (by positivity)
      have hB : (0 : ℝ) < Real.sqrt (1 + ‖b‖ ^ 2) :=
        Real.sqrt_pos.mpr (by positivity)
      have hprod : (0 : ℝ) < Real.sqrt (1 + ‖a‖ ^ 2) * Real.sqrt (1 + ‖b‖ ^ 2) :=
        mul_pos hA hB
      rw [div_le_iff₀ hprod]
      -- Chordal expansion: ‖a - b‖² = ‖a‖² + ‖b‖² - 2 * (a * conj b).re
      have hexpand : ‖a - b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * (a * (starRingEnd ℂ) b).re := by
        rw [Complex.sq_norm, Complex.normSq_sub, ← Complex.sq_norm a, ← Complex.sq_norm b]
      -- Lower bound: (a * conj b).re ≥ -‖a‖·‖b‖
      have hre_lower : -(‖a‖ * ‖b‖) ≤ (a * (starRingEnd ℂ) b).re := by
        have h1 : (-(a * (starRingEnd ℂ) b)).re ≤ ‖-(a * (starRingEnd ℂ) b)‖ :=
          Complex.re_le_norm _
        simp only [Complex.neg_re, norm_neg, norm_mul, RCLike.norm_conj] at h1
        linarith
      -- AM-GM: 2‖a‖‖b‖ ≤ 1 + ‖a‖²‖b‖²
      have h_amgm : 2 * (‖a‖ * ‖b‖) ≤ 1 + ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
        nlinarith [sq_nonneg (1 - ‖a‖ * ‖b‖)]
      -- Combine: ‖a-b‖² ≤ (1+‖a‖²)(1+‖b‖²)
      have sq_step : ‖a - b‖ ^ 2 ≤ (1 + ‖a‖ ^ 2) * (1 + ‖b‖ ^ 2) := by
        have hexp : (1 + ‖a‖ ^ 2) * (1 + ‖b‖ ^ 2)
            = 1 + ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖a‖ ^ 2 * ‖b‖ ^ 2 := by ring
        nlinarith [hexpand, hre_lower, h_amgm, sq_nonneg ‖a‖, sq_nonneg ‖b‖, hexp]
      -- Square-root: ‖a-b‖ ≤ √((1+‖a‖²)(1+‖b‖²)) = √(1+‖a‖²) · √(1+‖b‖²)
      have norm_nn : 0 ≤ ‖a - b‖ := norm_nonneg _
      have sqrt_step : ‖a - b‖ ≤ Real.sqrt ((1 + ‖a‖ ^ 2) * (1 + ‖b‖ ^ 2)) := by
        rw [← Real.sqrt_sq norm_nn]
        exact Real.sqrt_le_sqrt sq_step
      have sqrt_split :
          Real.sqrt ((1 + ‖a‖ ^ 2) * (1 + ‖b‖ ^ 2))
            = Real.sqrt (1 + ‖a‖ ^ 2) * Real.sqrt (1 + ‖b‖ ^ 2) :=
        Real.sqrt_mul (by positivity) _
      linarith [sqrt_step, sqrt_split]
  | OnePoint.some a, ∞ =>
      simp only [sphericalDist, chordalDistInfty]
      have hpos : (0 : ℝ) < Real.sqrt (1 + ‖a‖ ^ 2) :=
        Real.sqrt_pos.mpr (by positivity)
      rw [div_le_iff₀ hpos]
      have h1 : (1 : ℝ) ≤ Real.sqrt (1 + ‖a‖ ^ 2) :=
        Real.one_le_sqrt.mpr (by linarith [sq_nonneg ‖a‖])
      linarith
  | ∞, OnePoint.some b =>
      simp only [sphericalDist, chordalDistInfty]
      have hpos : (0 : ℝ) < Real.sqrt (1 + ‖b‖ ^ 2) :=
        Real.sqrt_pos.mpr (by positivity)
      rw [div_le_iff₀ hpos]
      have h1 : (1 : ℝ) ≤ Real.sqrt (1 + ‖b‖ ^ 2) :=
        Real.one_le_sqrt.mpr (by linarith [sq_nonneg ‖b‖])
      linarith
  | ∞, ∞ =>
      simp only [sphericalDist]
      norm_num

/-- The spherical metric induces the one-point-compactification topology on `ℂ̂`. -/
theorem sphericalDist_induces_topology :
    ∀ s : Set ℂ̂, IsOpen s ↔
      ∀ z ∈ s, ∃ ε > 0, ∀ w, sphericalDist z w < ε → w ∈ s := by
  -- Step 1: Continuity of stereoEmbed.
  have hcont : Continuous stereoEmbed := by
    rw [OnePoint.continuous_iff]
    refine ⟨?_, ?_⟩
    · -- Tendsto at ∞: as ‖w‖ → ∞, stereoEmbed ↑w → stereoEmbed ∞.
      rw [Filter.coclosedCompact_eq_cocompact, Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop (2 / ε)] with w hw
      have heq : dist (stereoEmbed (↑w : ℂ̂)) (stereoEmbed ∞) = chordalDistInfty w := by
        rw [dist_stereoEmbed_eq_sphericalDist]; rfl
      rw [heq]
      unfold chordalDistInfty
      have hsqrt : (0 : ℝ) < Real.sqrt (1 + ‖w‖^2) := Real.sqrt_pos.mpr (by positivity)
      rw [div_lt_iff₀ hsqrt]
      have h_norm_le : ‖w‖ ≤ Real.sqrt (1 + ‖w‖^2) := by
        have h_sq : ‖w‖^2 ≤ 1 + ‖w‖^2 := by linarith
        calc ‖w‖ = Real.sqrt (‖w‖^2) := (Real.sqrt_sq (norm_nonneg w)).symm
          _ ≤ Real.sqrt (1 + ‖w‖^2) := Real.sqrt_le_sqrt h_sq
      have h_pos_w : (0 : ℝ) < ‖w‖ := by linarith [hw, div_pos (by norm_num : (0:ℝ) < 2) hε]
      have h_two_lt : 2 < ε * ‖w‖ := by
        rw [show (2 : ℝ) = (2 / ε) * ε from by field_simp]
        nlinarith [hw, hε]
      have h_mul_le : ε * ‖w‖ ≤ ε * Real.sqrt (1 + ‖w‖^2) :=
        mul_le_mul_of_nonneg_left h_norm_le hε.le
      calc (2 : ℝ) < ε * ‖w‖ := h_two_lt
        _ ≤ ε * Real.sqrt (1 + ‖w‖^2) := h_mul_le
    · -- Continuity on finite ℂ.
      unfold stereoEmbed
      apply Continuous.comp (ContinuousLinearEquiv.continuous _)
      refine continuous_pi (fun i => ?_)
      fin_cases i
      · -- Component 0
        apply Continuous.div (by fun_prop) (by fun_prop)
        intro w; positivity
      · -- Component 1
        apply Continuous.div (by fun_prop) (by fun_prop)
        intro w; positivity
      · -- Component 2
        apply Continuous.div (by fun_prop) (by fun_prop)
        intro w; positivity
  -- Step 2: Injectivity of stereoEmbed.
  have hinj : Function.Injective stereoEmbed := by
    intro z w hzw
    have h1 : dist (stereoEmbed z) (stereoEmbed w) = 0 := by rw [hzw, dist_self]
    rw [dist_stereoEmbed_eq_sphericalDist] at h1
    exact (sphericalDist_eq_zero_iff z w).mp h1
  -- Step 3: IsClosedEmbedding → IsInducing.
  have hinduce : Topology.IsInducing stereoEmbed :=
    (hcont.isClosedEmbedding hinj).isInducing
  -- Step 4: Convert IsOpen via the embedding + metric.
  intro s
  rw [hinduce.isOpen_iff]
  constructor
  · -- (→) ∃ open t, preimage = s ⟹ chordal ball property
    rintro ⟨t, htopen, htpre⟩ z hz
    have hszt : stereoEmbed z ∈ t := by
      have : z ∈ stereoEmbed ⁻¹' t := htpre.symm ▸ hz
      exact this
    rcases Metric.isOpen_iff.mp htopen (stereoEmbed z) hszt with ⟨ε, hε, hball⟩
    refine ⟨ε, hε, fun w hw => ?_⟩
    have hdist : dist (stereoEmbed z) (stereoEmbed w) < ε := by
      rw [dist_stereoEmbed_eq_sphericalDist]; exact hw
    have hwt : stereoEmbed w ∈ t := hball (by
      rw [Metric.mem_ball, dist_comm]; exact hdist)
    have : w ∈ stereoEmbed ⁻¹' t := hwt
    rwa [htpre] at this
  · -- (←) chordal ball property ⟹ ∃ open t, preimage = s
    intro hballs
    choose εf hε hballs' using hballs
    refine ⟨⋃ (z : ℂ̂) (hz : z ∈ s), Metric.ball (stereoEmbed z) (εf z hz), ?_, ?_⟩
    · -- union of open balls is open
      apply isOpen_iUnion; intro z
      apply isOpen_iUnion; intro hz
      exact Metric.isOpen_ball
    · -- preimage = s
      ext w
      simp only [Set.mem_preimage, Set.mem_iUnion, Metric.mem_ball]
      constructor
      · rintro ⟨z, hz, hwz⟩
        have hd : sphericalDist z w < εf z hz := by
          rw [← dist_stereoEmbed_eq_sphericalDist, dist_comm]; exact hwz
        exact hballs' z hz w hd
      · intro hws
        refine ⟨w, hws, ?_⟩
        rw [dist_self]; exact hε w hws

/-! ## Access lemmas and the Euclidean comparison -/

/-- The spherical distance between finite points is the chordal distance. -/
theorem sphericalDist_coe_coe (z w : ℂ) :
    sphericalDist (z : ℂ̂) (w : ℂ̂) = chordalDist z w := rfl

/-- The spherical distance from a finite point to `∞`. -/
theorem sphericalDist_coe_infty (z : ℂ) :
    sphericalDist (z : ℂ̂) (∞ : ℂ̂) = chordalDistInfty z := rfl

/-- On a norm-bounded region, the Euclidean distance is controlled by the
spherical (chordal) distance: the chordal denominators are at most
`1 + M ^ 2`. -/
theorem norm_sub_le_sphericalDist_mul {z w : ℂ} {M : ℝ} (hz : ‖z‖ ≤ M)
    (hw : ‖w‖ ≤ M) :
    ‖z - w‖ ≤ (1 + M ^ 2) / 2 * sphericalDist (z : ℂ̂) (w : ℂ̂) := by
  rw [sphericalDist_coe_coe]
  unfold chordalDist
  have hposz : (0 : ℝ) < Real.sqrt (1 + ‖z‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hposw : (0 : ℝ) < Real.sqrt (1 + ‖w‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hprod_pos : (0 : ℝ) < Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2) :=
    mul_pos hposz hposw
  have hz2 : Real.sqrt (1 + ‖z‖ ^ 2) ≤ Real.sqrt (1 + M ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [norm_nonneg z])
  have hw2 : Real.sqrt (1 + ‖w‖ ^ 2) ≤ Real.sqrt (1 + M ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [norm_nonneg w])
  have hMsq : Real.sqrt (1 + M ^ 2) * Real.sqrt (1 + M ^ 2) = 1 + M ^ 2 := by
    rw [← pow_two, Real.sq_sqrt (by positivity)]
  have hprod_le : Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2) ≤ 1 + M ^ 2 := by
    calc Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2)
        ≤ Real.sqrt (1 + M ^ 2) * Real.sqrt (1 + M ^ 2) :=
          mul_le_mul hz2 hw2 hposw.le (Real.sqrt_nonneg _)
      _ = 1 + M ^ 2 := hMsq
  rw [← mul_div_assoc, le_div_iff₀ hprod_pos]
  nlinarith [mul_nonneg (norm_nonneg (z - w)) (sub_nonneg.mpr hprod_le)]

end RiemannDynamics
