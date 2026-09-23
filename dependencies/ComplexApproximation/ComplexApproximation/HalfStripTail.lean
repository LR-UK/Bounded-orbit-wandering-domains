import ComplexApproximation.HalfStripNormalisation

/-! # Uniform rightward escape along a closed half-strip -/

open Set Metric Complex Filter
open scoped Topology NNReal

namespace ComplexApproximation

theorem uniform_re_escape_of_halfStrip_extension {f : ℂ → ℂ} {a b : ℝ}
    (hb : 0 ≤ b) (H : ℂ ≃ₜ ℂ) (heq : EqOn f H (closedRightHalfStrip a b))
    {L : ℝ≥0} (hL : LipschitzWith L H)
    (ht : Tendsto (fun x : ℝ => (f x).re) atTop atTop) :
    ∀ B : ℝ, ∃ X : ℝ, ∀ z ∈ closedRightHalfStrip a b, X ≤ z.re → B ≤ (f z).re := by
  intro B
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp (ht.eventually (eventually_ge_atTop (B + L * b)))
  refine ⟨X, ?_⟩
  intro z hz hzr
  have hzaxis : (z.re : ℂ) ∈ closedRightHalfStrip a b := ⟨hz.1, by simpa using hb⟩
  have hn := hL.dist_le_mul z (z.re : ℂ)
  rw [← heq hz, ← heq hzaxis, dist_eq_norm, dist_eq_norm] at hn
  have hid : z - (z.re : ℂ) = (z.im : ℂ) * I := by apply Complex.ext <;> simp
  rw [hid, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at hn
  have hn' : ‖f z - f (z.re : ℂ)‖ ≤ (L : ℝ) * b :=
    hn.trans (mul_le_mul_of_nonneg_left hz.2 L.coe_nonneg)
  have hr := (abs_le.mp ((Complex.abs_re_le_norm (f z - f (z.re : ℂ))).trans hn')).1
  simp only [Complex.sub_re] at hr
  linarith [hX z.re hzr]

namespace HalfStrip

theorem tendsto_re_normalizedMap_atTop {c ρ η : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun x : ℝ => (normalizedMap c ρ η x).re) atTop atTop := by
  apply (tendsto_scaled_profile_atTop (η := η) hρ).congr'
  filter_upwards [eventually_ge_atTop (1 - η)] with x hx
  rw [normalizedMap_ofReal (by linarith : 0 < x + η)]
  simp

theorem uniform_re_escape_normalizedMap {a b c ρ η : ℝ}
    (ha : 0 < a + η) (hb : 0 ≤ b) (hbpi : b < Real.pi / 2) (hρ : 0 < ρ) :
    ∀ B : ℝ, ∃ X : ℝ, ∀ z ∈ closedRightHalfStrip a b,
      X ≤ z.re → B ≤ (normalizedMap c ρ η z).re := by
  obtain ⟨H, heq, L, L', hL, _⟩ := exists_bilipschitz_normalized_extension
    (c := c) ha hb hbpi hρ
  exact uniform_re_escape_of_halfStrip_extension hb H heq hL (tendsto_re_normalizedMap_atTop hρ)

end HalfStrip

end ComplexApproximation
