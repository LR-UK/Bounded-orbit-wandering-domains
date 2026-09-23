import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.MetricSpace.Lipschitz

/-! # The nonexpansive projection onto a closed horizontal half-strip -/

open Set Metric Complex
open scoped NNReal

namespace ComplexApproximation

def closedRightHalfStrip (a b : ℝ) : Set ℂ := {z | a ≤ z.re ∧ |z.im| ≤ b}

def halfStripProjection (a b : ℝ) (z : ℂ) : ℂ :=
  ⟨max a z.re, min b (max (-b) z.im)⟩

theorem halfStripProjection_mem (a : ℝ) {b : ℝ} (hb : 0 ≤ b) (z : ℂ) :
    halfStripProjection a b z ∈ closedRightHalfStrip a b := by
  refine ⟨le_max_left _ _, abs_le.mpr ⟨?_, min_le_left _ _⟩⟩
  exact le_min (by linarith) (le_max_left _ _)

theorem halfStripProjection_eq {a b : ℝ} {z : ℂ} (hz : z ∈ closedRightHalfStrip a b) :
    halfStripProjection a b z = z := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hz.2
  apply Complex.ext <;> simp only [halfStripProjection]
  · exact max_eq_right hz.1
  · rw [max_eq_right hlo, min_eq_right hhi]

theorem lipschitzWith_halfStripProjection (a b : ℝ) :
    LipschitzWith 1 (halfStripProjection a b) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hre := ((LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).const_max a).dist_le_mul z.re w.re
  have him := (((LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).const_max (-b)).min_const b).dist_le_mul z.im w.im
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, id_eq] at hre him
  rw [min_comm (max (-b) z.im), min_comm (max (-b) w.im)] at him
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have hs (v : ℂ) : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, pow_two]
  have hr2 : (max a z.re - max a w.re) ^ 2 ≤ (z.re - w.re) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hre
  have hi2 : (min b (max (-b) z.im) - min b (max (-b) w.im)) ^ 2 ≤ (z.im - w.im) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr him
  have hsq : ‖halfStripProjection a b z - halfStripProjection a b w‖ ^ 2 ≤ ‖z - w‖ ^ 2 := by
    simp only [hs, Complex.sub_re, Complex.sub_im, halfStripProjection]
    linarith
  nlinarith [norm_nonneg (halfStripProjection a b z - halfStripProjection a b w), norm_nonneg (z - w)]

theorem convex_closedRightHalfStrip (a b : ℝ) : Convex ℝ (closedRightHalfStrip a b) := by
  have he : closedRightHalfStrip a b = {z : ℂ | a ≤ z.re} ∩
      ({z : ℂ | -b ≤ z.im} ∩ {z : ℂ | z.im ≤ b}) := by
    ext z
    simp [closedRightHalfStrip, abs_le]
  rw [he]
  exact (convex_halfSpace_re_ge a).inter
    ((convex_halfSpace_im_ge _).inter (convex_halfSpace_im_le _))

end ComplexApproximation
