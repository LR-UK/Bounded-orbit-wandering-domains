import ComplexApproximation.BiLipschitzExtension

/-! # Quantitative extensions from complete horizontal strips -/

open Set Metric Complex
open scoped NNReal

namespace ComplexApproximation

def closedHorizontalStrip (l u : ℝ) : Set ℂ := {z | l ≤ z.im ∧ z.im ≤ u}

def horizontalStripProjection (l u : ℝ) (z : ℂ) : ℂ :=
  ⟨z.re, min u (max l z.im)⟩

theorem horizontalStripProjection_mem {l u : ℝ} (hlu : l ≤ u) (z : ℂ) :
    horizontalStripProjection l u z ∈ closedHorizontalStrip l u :=
  ⟨le_min hlu (le_max_left _ _), min_le_left _ _⟩

theorem horizontalStripProjection_eq {l u : ℝ} {z : ℂ}
    (hz : z ∈ closedHorizontalStrip l u) : horizontalStripProjection l u z = z := by
  apply Complex.ext
  · rfl
  · change min u (max l z.im) = z.im
    rw [max_eq_right hz.1, min_eq_right hz.2]

theorem lipschitzWith_horizontalStripProjection (l u : ℝ) :
    LipschitzWith 1 (horizontalStripProjection l u) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have him := (((LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).const_max l).min_const u).dist_le_mul z.im w.im
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, id_eq] at him
  rw [min_comm (max l z.im), min_comm (max l w.im)] at him
  have hi2 : (min u (max l z.im) - min u (max l w.im)) ^ 2 ≤ (z.im - w.im) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr him
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    horizontalStripProjection]
  nlinarith

theorem convex_closedHorizontalStrip (l u : ℝ) : Convex ℝ (closedHorizontalStrip l u) :=
  (convex_halfSpace_im_ge l).inter (convex_halfSpace_im_le u)

theorem exists_bilipschitz_extension_on_horizontalStrip {l u : ℝ} (hlu : l ≤ u)
    {f : ℂ → ℂ} (hf : ∀ z ∈ closedHorizontalStrip l u, DifferentiableAt ℂ f z)
    {m M : ℝ} (hm : 0 < m)
    (hderiv : ∀ z ∈ closedHorizontalStrip l u, m ≤ (deriv f z).re ∧ ‖deriv f z‖ ≤ M) :
    ∃ H : ℂ ≃ₜ ℂ, EqOn f H (closedHorizontalStrip l u) ∧ ∃ L L' : ℝ≥0,
      LipschitzWith L H ∧ LipschitzWith L' H.symm :=
  exists_bilipschitz_extension_of_positive_derivative
    (convex_closedHorizontalStrip l u) (lipschitzWith_horizontalStripProjection l u)
    (fun z _ => horizontalStripProjection_mem hlu z)
    (fun _ hz => horizontalStripProjection_eq hz) hf hm hderiv

end ComplexApproximation
