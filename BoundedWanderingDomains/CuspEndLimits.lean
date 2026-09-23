/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.CuspLogLimit
import BoundedWanderingDomains.LogBarrier

open Set Filter Metric
open scoped Topology

namespace AreaDeficit

/-- The logarithm of the covering density has coefficient minus one at a finite cusp. -/
theorem IsHolomorphicDiscCovering.log_density_finite_cusp {p : ℂ → ℂ} {S : Set ℂ}
    (hp : IsHolomorphicDiscCovering p S) {a b : ℂ} (hab : a ≠ b)
    (ha : a ∉ S) (hb : b ∉ S) {R : ℝ} (hR : 0 < R)
    (hball : ball a R \ {a} ⊆ S) :
    Tendsto (fun z : ℂ =>
      (Real.log (coveringDensity p z) + Real.log ‖z - a‖) / (-Real.log ‖z - a‖))
      (𝓝[≠] a) (𝓝 0) := by
  have hd : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  have ht := tendsto_neg_atBot_atTop.comp (log_norm_tendsto_atBot a)
  have hr : Tendsto (fun z : ℂ => ‖z - a‖) (𝓝[≠] a) (𝓝 0) := by
    simpa using ((continuousAt_id.sub (show ContinuousAt (fun _ : ℂ => a) a from continuousAt_const)).norm.tendsto.mono_left
      (show 𝓝[≠] a ≤ 𝓝 a from nhdsWithin_le_nhds))
  have he : ∀ᶠ z in 𝓝[≠] a, z ≠ a ∧ ‖z - a‖ < R ∧ ‖z - a‖ ≤ ‖b - a‖ := by
    filter_upwards [self_mem_nhdsWithin, hr.eventually (eventually_lt_nhds hR),
      hr.eventually (eventually_lt_nhds hd)] with z hz hzR hzd
    exact ⟨hz, hzR, hzd.le⟩
  have hs : ∀ᶠ z in 𝓝[≠] a, z ∈ S := by
    filter_upwards [he] with z hz
    exact hball ⟨mem_ball_iff_norm.mpr hz.2.1, hz.1⟩
  have hq : ∀ᶠ z in 𝓝[≠] a, 0 < coveringDensity p z * ‖z - a‖ := by
    filter_upwards [he, hs] with z hz hzs
    exact mul_pos (hp.density_pos hzs) (norm_pos_iff.mpr (sub_ne_zero.mpr hz.1))
  have hl : ∀ᶠ z in 𝓝[≠] a,
      1 / (4 * ((cuspConstant + Real.log ‖b - a‖) + -Real.log ‖z - a‖)) ≤
        coveringDensity p z * ‖z - a‖ := by
    filter_upwards [he, hs] with z hz hzs
    have hrp : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz.1)
    have h := mul_le_mul_of_nonneg_right
      (hp.density_lower_cusp_pair hab ha hb hzs hz.2.2) hrp.le
    convert h using 1
    rw [Real.log_div hrp.ne' hd.ne']
    field_simp
    ring
  have hu : ∀ᶠ z in 𝓝[≠] a,
      coveringDensity p z * ‖z - a‖ ≤ 2 / (Real.log R + -Real.log ‖z - a‖) := by
    filter_upwards [he] with z hz
    have hrp : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz.1)
    have h := mul_le_mul_of_nonneg_right
      (hp.density_upper_cusp hball hz.1 hz.2.1) hrp.le
    convert h using 1
    rw [Real.log_div hR.ne' hrp.ne']
    field_simp
    ring
  have H := tendsto_log_of_cusp_bounds ht hq hl hu
  apply H.congr'
  filter_upwards [he, hs] with z hz hzs
  rw [Real.log_mul (hp.density_pos hzs).ne'
    (norm_pos_iff.mpr (sub_ne_zero.mpr hz.1)).ne']
  rfl

/-- The same coefficient at infinity, expressed for any filter escaping the centre. -/
theorem IsHolomorphicDiscCovering.log_density_infinite_cusp {p : ℂ → ℂ} {S : Set ℂ}
    (hp : IsHolomorphicDiscCovering p S) {a b : ℂ} (hab : a ≠ b)
    (ha : a ∉ S) (hb : b ∉ S) {R : ℝ} (hR : 0 < R)
    (hout : {w : ℂ | R < ‖w - a‖} ⊆ S) {l : Filter ℂ}
    (hr : Tendsto (fun z : ℂ => ‖z - a‖) l atTop) :
    Tendsto (fun z : ℂ =>
      (Real.log (coveringDensity p z) + Real.log ‖z - a‖) / Real.log ‖z - a‖)
      l (𝓝 0) := by
  have hd : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  have ht := Real.tendsto_log_atTop.comp hr
  have he : ∀ᶠ z in l, R < ‖z - a‖ ∧ ‖b - a‖ ≤ ‖z - a‖ :=
    (hr.eventually_gt_atTop R).and (hr.eventually_ge_atTop ‖b - a‖)
  have hq : ∀ᶠ z in l, 0 < coveringDensity p z * ‖z - a‖ := by
    filter_upwards [he] with z hz
    exact mul_pos (hp.density_pos (hout hz.1)) (hR.trans hz.1)
  have hl : ∀ᶠ z in l,
      1 / (4 * ((cuspConstant - Real.log ‖b - a‖) + Real.log ‖z - a‖)) ≤
        coveringDensity p z * ‖z - a‖ := by
    filter_upwards [he] with z hz
    have hrp : 0 < ‖z - a‖ := hR.trans hz.1
    have h := mul_le_mul_of_nonneg_right
      (hp.density_lower_cusp_outside hab ha hb (hout hz.1) hz.2) hrp.le
    convert h using 1
    rw [Real.log_div hd.ne' hrp.ne']
    field_simp
    ring
  have hu : ∀ᶠ z in l,
      coveringDensity p z * ‖z - a‖ ≤ 2 / (-Real.log R + Real.log ‖z - a‖) := by
    filter_upwards [he] with z hz
    have hrp : 0 < ‖z - a‖ := hR.trans hz.1
    have h := mul_le_mul_of_nonneg_right
      (hp.density_upper_cusp_outside hR hout hz.1) hrp.le
    convert h using 1
    rw [Real.log_div hrp.ne' hR.ne']
    field_simp
    ring
  have H := tendsto_log_of_cusp_bounds ht hq hl hu
  apply H.congr'
  filter_upwards [he] with z hz
  rw [Real.log_mul (hp.density_pos (hout hz.1)).ne' (hR.trans hz.1).ne']
  rfl

end AreaDeficit
