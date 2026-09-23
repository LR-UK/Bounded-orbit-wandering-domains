import ComplexApproximation.HalfStripExtension
import Mathlib.Topology.Order.Compact

/-! # Normalising the explicit half-strip map

Positive real intervals can be compressed uniformly while a small horizontal
shift sends the endpoint arbitrarily far to the left.
-/

open Set Metric Complex Filter
open scoped Topology NNReal

noncomputable section

namespace ComplexApproximation.HalfStrip

def realProfile (x : ℝ) : ℝ := Real.log (Real.sinh x) - Real.log (Real.sinh 1)

theorem continuousOn_realProfile : ContinuousOn realProfile (Ioi 0) := by
  intro x hx
  exact (((Real.continuousAt_log (Real.sinh_pos_iff.mpr hx).ne').comp
    Real.continuous_sinh.continuousAt).sub continuousAt_const).continuousWithinAt

theorem exists_compression {a b r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ * (Real.pi / 2) < r ∧
      ∀ x ∈ Icc a b, ∀ η ∈ Icc (0 : ℝ) 1, |ρ * realProfile (x + η)| < 1 / 2 := by
  have hcont : ContinuousOn realProfile (Icc a (b + 1)) :=
    continuousOn_realProfile.mono (fun _ hx => ha.trans_le hx.1)
  obtain ⟨M, hM, hbound⟩ := (isCompact_Icc.image_of_continuousOn hcont).isBounded.exists_pos_norm_le
  let ρ := min (r / (Real.pi + 1)) (1 / (4 * (M + 1)))
  have hρ : 0 < ρ := lt_min (div_pos hr (by linarith [Real.pi_pos])) (by positivity)
  have hρ₁ : ρ * (Real.pi + 1) ≤ r :=
    (le_div_iff₀ (by linarith [Real.pi_pos])).mp (min_le_left _ _)
  have hρ₂ : ρ * (4 * (M + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  refine ⟨ρ, hρ, by nlinarith [Real.pi_pos], ?_⟩
  intro x hx η hη
  have hmem : x + η ∈ Icc a (b + 1) := ⟨by linarith [hx.1, hη.1], by linarith [hx.2, hη.2]⟩
  have hbnd : |realProfile (x + η)| ≤ M := by
    simpa only [Real.norm_eq_abs] using hbound _ (mem_image_of_mem realProfile hmem)
  rw [abs_mul, abs_of_pos hρ]
  have := mul_le_mul_of_nonneg_left hbnd hρ.le
  nlinarith

theorem tendsto_scaled_profile_at_zero {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun x : ℝ => ρ * realProfile x) (𝓝[>] 0) atBot := by
  apply Filter.tendsto_atBot.mpr
  intro B
  filter_upwards [tendsto_real_map_at_zero.eventually
    (eventually_le_atBot (B / ρ + Real.log (Real.sinh 1)))] with x hx
  have h := mul_le_mul_of_nonneg_left hx hρ.le
  have hdiv : ρ * (B / ρ) = B := by field_simp
  dsimp [realProfile]
  nlinarith

theorem exists_small_shift_far_left {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (B : ℝ) :
    ∃ η : ℝ, 0 < η ∧ η < σ ∧ ρ * realProfile η < B := by
  have he : ∀ᶠ η : ℝ in 𝓝[>] 0, ρ * realProfile η < B :=
    (tendsto_scaled_profile_at_zero hρ).eventually (eventually_lt_atBot B)
  have hs : ∀ᶠ η : ℝ in 𝓝[>] 0, η < σ :=
    (eventually_lt_nhds hσ).filter_mono nhdsWithin_le_nhds
  have hp : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η := self_mem_nhdsWithin
  obtain ⟨η, hη, hησ, hηB⟩ := (hp.and (hs.and he)).exists
  exact ⟨η, hη, hησ, hηB⟩

theorem tendsto_scaled_profile_atTop {ρ η : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun x : ℝ => ρ * realProfile (x + η)) atTop atTop := by
  have hshift : Tendsto (fun x : ℝ => x + η) atTop atTop :=
    tendsto_atTop_add_const_right atTop η tendsto_id
  have ht := tendsto_real_map_atTop.comp hshift
  apply Filter.tendsto_atTop.mpr
  intro B
  filter_upwards [ht.eventually (eventually_ge_atTop (B / ρ + Real.log (Real.sinh 1)))] with x hx
  have h := mul_le_mul_of_nonneg_left hx hρ.le
  have hdiv : ρ * (B / ρ) = B := by field_simp
  dsimp only [Function.comp_apply] at h
  dsimp [realProfile]
  nlinarith

def normalizedMap (c ρ η : ℝ) (z : ℂ) : ℂ :=
  (ρ : ℂ) * (map (z + (η : ℂ)) - map 1) + (c : ℂ) * I

theorem normalizedMap_ofReal {c ρ η x : ℝ} (hx : 0 < x + η) :
    normalizedMap c ρ η x = (ρ * realProfile (x + η) : ℝ) + (c : ℂ) * I := by
  have hmap1 : map 1 = (Real.log (Real.sinh 1) : ℂ) := by
    simpa only [Complex.ofReal_one] using map_ofReal (by norm_num : (0 : ℝ) < 1)
  rw [normalizedMap, ← Complex.ofReal_add, map_ofReal hx, hmap1]
  simp only [realProfile, Complex.ofReal_sub, Complex.ofReal_mul]

theorem normalizedMap_im_bound {c ρ η r : ℝ} (hρ : 0 < ρ)
    (hρr : ρ * (Real.pi / 2) < r) {z : ℂ} (hz : z + (η : ℂ) ∈ domain) :
    |(normalizedMap c ρ η z).im - c| < r := by
  have hmap1 : (map 1).im = 0 := by
    have h := map_ofReal (by norm_num : (0 : ℝ) < 1)
    simpa only [Complex.ofReal_one, Complex.ofReal_im] using congrArg Complex.im h
  have hm := abs_im_map_lt hz
  simp only [normalizedMap, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_im, hmap1, Complex.I_im, Complex.I_re,
    mul_one, zero_mul, add_zero, sub_zero, add_sub_cancel_right, abs_mul, abs_of_pos hρ]
  exact (mul_lt_mul_of_pos_left hm hρ).trans hρr

theorem hasDerivAt_normalizedMap {c ρ η : ℝ} {z : ℂ} (hz : z + (η : ℂ) ∈ domain) :
    HasDerivAt (normalizedMap c ρ η) ((ρ : ℂ) * deriv map (z + (η : ℂ))) z := by
  have hm := (hasDerivAt_map hz).comp z ((hasDerivAt_id z).add_const (η : ℂ))
  have h := ((hm.sub_const (map 1)).const_mul (ρ : ℂ)).add_const ((c : ℂ) * I)
  convert h using 1 <;>
    simp only [mul_one, ← (hasDerivAt_map hz).deriv, Function.comp_def, id_eq]
  rfl

theorem exists_bilipschitz_normalized_extension {a b c ρ η : ℝ}
    (ha : 0 < a + η) (hb : 0 ≤ b) (hbpi : b < Real.pi / 2) (hρ : 0 < ρ) :
    ∃ H : ℂ ≃ₜ ℂ, EqOn (normalizedMap c ρ η) H (closedRightHalfStrip a b) ∧
      ∃ L L' : ℝ≥0, LipschitzWith L H ∧ LipschitzWith L' H.symm := by
  let q := Real.exp (-2 * (a + η))
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  let m := (1 - q) / (1 + q)
  let M := (1 + q) / (1 - q)
  have hm : 0 < m := div_pos (sub_pos.mpr hq) (by dsimp [q]; positivity)
  have hsub : ∀ z ∈ closedRightHalfStrip a b, z + (η : ℂ) ∈ domain := by
    intro z hz
    exact ⟨by change 0 < z.re + η; linarith [hz.1], by simpa using hz.2.trans_lt hbpi⟩
  apply exists_bilipschitz_extension_of_positive_derivative
    (convex_closedRightHalfStrip a b) (lipschitzWith_halfStripProjection a b)
    (fun z _ => halfStripProjection_mem a hb z) (fun _ hz => halfStripProjection_eq hz)
    (fun _ hz => (hasDerivAt_normalizedMap (hsub _ hz)).differentiableAt) (mul_pos hρ hm)
  intro z hz
  have hzre : a + η ≤ (z + (η : ℂ)).re := by change a + η ≤ z.re + η; linarith [hz.1]
  rw [(hasDerivAt_normalizedMap (hsub z hz)).deriv]
  constructor
  · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      using mul_le_mul_of_nonneg_left (re_derivative_lower_bound ha (hsub z hz) hzre) hρ.le
  · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    exact mul_le_mul_of_nonneg_left (derivative_bounds ha (hsub z hz) hzre).2 hρ.le

end ComplexApproximation.HalfStrip
