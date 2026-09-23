/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.CuspDensityBounds

open Set Metric Function

namespace AreaDeficit

/-- The logarithmic derivative estimate with an arbitrary pair of omitted values. -/
theorem norm_deriv_le_cusp_bound_pair {f : ℂ → ℂ} {a b : ℂ} (hab : a ≠ b)
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (ha : ∀ z ∈ ball 0 1, f z ≠ a) (hb : ∀ z ∈ ball 0 1, f z ≠ b)
    (hbase : ‖f 0 - a‖ ≤ ‖b - a‖) :
    ‖deriv f 0‖ ≤ 8 * ‖f 0 - a‖ *
      (cuspConstant - Real.log (‖f 0 - a‖ / ‖b - a‖)) := by
  have hc : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hcn : 0 < ‖b - a‖ := norm_pos_iff.mpr hc
  let g : ℂ → ℂ := fun z => (f z - a) / (b - a)
  have hg : DifferentiableOn ℂ g (ball 0 1) := (hf.sub_const a).div_const _
  have hga : ∀ z ∈ ball 0 1, g z ≠ 0 := by
    intro z hz
    exact div_ne_zero (sub_ne_zero.mpr (ha z hz)) hc
  have hgb : ∀ z ∈ ball 0 1, g z ≠ 1 := by
    intro z hz he
    have he' : f z - a = b - a := (div_eq_one_iff_eq hc).mp he
    exact hb z hz (sub_left_injective he')
  have hg0 : ‖g 0‖ = ‖f 0 - a‖ / ‖b - a‖ := norm_div _ _
  have hgn : ‖g 0‖ ≤ 1 := by rw [hg0]; exact (div_le_one hcn).mpr hbase
  have hd := norm_deriv_le_cusp_bound hg hga hgb hgn
  have he : deriv g 0 = deriv f 0 / (b - a) := by
    dsimp [g]
    rw [deriv_div_const, deriv_sub_const]
  rw [he, norm_div, hg0] at hd
  have H := (div_le_iff₀ hcn).mp hd
  convert H using 1
  field_simp

/-- Lower cusp estimate at any omitted point, using a second omitted point for scale. -/
theorem IsHolomorphicDiscCovering.density_lower_cusp_pair {p : ℂ → ℂ} {S : Set ℂ}
    (hp : IsHolomorphicDiscCovering p S) {a b : ℂ} (hab : a ≠ b)
    (ha : a ∉ S) (hb : b ∉ S) {z : ℂ} (hz : z ∈ S)
    (hzn : ‖z - a‖ ≤ ‖b - a‖) :
    1 / (4 * ‖z - a‖ * (cuspConstant - Real.log (‖z - a‖ / ‖b - a‖))) ≤
      coveringDensity p z := by
  obtain ⟨g, hg, hgm, hg0, he⟩ := hp.density_extremal hz
  have hd := norm_deriv_le_cusp_bound_pair hab hg
    (fun w hw hh => ha (hh ▸ hgm hw)) (fun w hw hh => hb (hh ▸ hgm hw))
    (by simpa [hg0] using hzn)
  rw [hg0] at hd
  have hzp : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (ne_of_mem_of_not_mem hz ha))
  have hcp : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  have hlog : Real.log (‖z - a‖ / ‖b - a‖) ≤ 0 :=
    Real.log_nonpos (by positivity) ((div_le_one hcp).mpr hzn)
  have hden : 0 < 4 * ‖z - a‖ * (cuspConstant - Real.log (‖z - a‖ / ‖b - a‖)) := by
    have : 0 < cuspConstant - Real.log (‖z - a‖ / ‖b - a‖) := by linarith [cuspConstant_pos]
    positivity
  apply (div_le_iff₀ hden).mpr
  have hm := mul_le_mul_of_nonneg_left hd (hp.density_pos hz).le
  rw [he] at hm
  nlinarith

/-- The companion derivative estimate when the centre value is far from the omitted pair. -/
theorem norm_deriv_le_cusp_bound_pair_outside {f : ℂ → ℂ} {a b : ℂ} (hab : a ≠ b)
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (ha : ∀ z ∈ ball 0 1, f z ≠ a) (hb : ∀ z ∈ ball 0 1, f z ≠ b)
    (hbase : ‖b - a‖ ≤ ‖f 0 - a‖) :
    ‖deriv f 0‖ ≤ 8 * ‖f 0 - a‖ *
      (cuspConstant - Real.log (‖b - a‖ / ‖f 0 - a‖)) := by
  have h0 : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hc : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hcn : 0 < ‖b - a‖ := norm_pos_iff.mpr hc
  have hv : f 0 - a ≠ 0 := sub_ne_zero.mpr (ha 0 h0)
  have hvn : 0 < ‖f 0 - a‖ := norm_pos_iff.mpr hv
  let g : ℂ → ℂ := fun z => (b - a) / (f z - a)
  have hg : DifferentiableOn ℂ g (ball 0 1) :=
    by
    intro z hz
    exact ((differentiableWithinAt_const (b - a)).div ((hf z hz).sub_const a)
      (sub_ne_zero.mpr (ha z hz)))
  have hga : ∀ z ∈ ball 0 1, g z ≠ 0 := by
    intro z hz
    exact div_ne_zero hc (sub_ne_zero.mpr (ha z hz))
  have hgb : ∀ z ∈ ball 0 1, g z ≠ 1 := by
    intro z hz he
    have he' : b - a = f z - a := (div_eq_one_iff_eq (sub_ne_zero.mpr (ha z hz))).mp he
    exact hb z hz (sub_left_injective he'.symm)
  have hg0 : ‖g 0‖ = ‖b - a‖ / ‖f 0 - a‖ := norm_div _ _
  have hgn : ‖g 0‖ ≤ 1 := by rw [hg0]; exact (div_le_one hvn).mpr hbase
  have hd := norm_deriv_le_cusp_bound hg hga hgb hgn
  have he : deriv g 0 = -(b - a) * deriv f 0 / (f 0 - a)^2 := by
    have H := (hasDerivAt_const (0 : ℂ) (b - a)).div
      ((hf.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt.sub_const a) hv
    convert H.deriv using 1
    ring
  rw [he, norm_div, norm_mul, norm_neg, norm_pow, hg0] at hd
  have H := mul_le_mul_of_nonneg_right hd (le_of_lt (div_pos (sq_pos_of_pos hvn) hcn))
  have hleft : (‖b - a‖ * ‖deriv f 0‖ / ‖f 0 - a‖ ^ 2) *
      (‖f 0 - a‖ ^ 2 / ‖b - a‖) = ‖deriv f 0‖ := by field_simp
  rw [hleft] at H
  convert H using 1
  field_simp

/-- Lower estimate at the infinite cusp, based on any two omitted finite values. -/
theorem IsHolomorphicDiscCovering.density_lower_cusp_outside {p : ℂ → ℂ} {S : Set ℂ}
    (hp : IsHolomorphicDiscCovering p S) {a b : ℂ} (hab : a ≠ b)
    (ha : a ∉ S) (hb : b ∉ S) {z : ℂ} (hz : z ∈ S)
    (hzn : ‖b - a‖ ≤ ‖z - a‖) :
    1 / (4 * ‖z - a‖ * (cuspConstant - Real.log (‖b - a‖ / ‖z - a‖))) ≤
      coveringDensity p z := by
  obtain ⟨g, hg, hgm, hg0, he⟩ := hp.density_extremal hz
  have hd := norm_deriv_le_cusp_bound_pair_outside hab hg
    (fun w hw hh => ha (hh ▸ hgm hw)) (fun w hw hh => hb (hh ▸ hgm hw))
    (by simpa [hg0] using hzn)
  rw [hg0] at hd
  have hzp : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (ne_of_mem_of_not_mem hz ha))
  have hcp : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  have hlog : Real.log (‖b - a‖ / ‖z - a‖) ≤ 0 :=
    Real.log_nonpos (by positivity) ((div_le_one hzp).mpr hzn)
  have hden : 0 < 4 * ‖z - a‖ * (cuspConstant - Real.log (‖b - a‖ / ‖z - a‖)) := by
    have : 0 < cuspConstant - Real.log (‖b - a‖ / ‖z - a‖) := by linarith [cuspConstant_pos]
    positivity
  apply (div_le_iff₀ hden).mpr
  have hm := mul_le_mul_of_nonneg_left hd (hp.density_pos hz).le
  rw [he] at hm
  nlinarith

/-- An exponential test disc gives the upper estimate at the infinite cusp. -/
theorem IsHolomorphicDiscCovering.density_upper_cusp_outside {p : ℂ → ℂ} {S : Set ℂ}
    (hp : IsHolomorphicDiscCovering p S) {a z : ℂ} {R : ℝ}
    (hR : 0 < R) (hout : {w : ℂ | R < ‖w - a‖} ⊆ S)
    (hzR : R < ‖z - a‖) :
    coveringDensity p z ≤ 2 / (‖z - a‖ * Real.log (‖z - a‖ / R)) := by
  have hr : 0 < ‖z - a‖ := hR.trans hzR
  have hz : z - a ≠ 0 := norm_pos_iff.mp hr
  let L : ℝ := Real.log (‖z - a‖ / R)
  have hL : 0 < L := Real.log_pos ((one_lt_div hR).mpr hzR)
  let g : ℂ → ℂ := fun w => a + (z - a) * Complex.exp ((L : ℂ) * w)
  have hg : Differentiable ℂ g := by dsimp [g]; fun_prop
  have hg0 : g 0 = z := by simp [g]
  have hgm : MapsTo g (ball 0 1) S := by
    intro w hw
    apply hout
    change R < ‖g w - a‖
    have he : g w - a = (z - a) * Complex.exp ((L : ℂ) * w) := by dsimp [g]; ring
    have hn : ‖g w - a‖ = ‖z - a‖ * Real.exp (L * w.re) := by
      rw [he, norm_mul, Complex.norm_exp]
      congr 2
      simp
    have hwre : -1 < w.re := by
      have h := Complex.re_le_norm (-w)
      simp only [Complex.neg_re, norm_neg] at h
      have hnw := mem_ball_zero_iff.mp hw
      linarith
    rw [hn]
    calc
      R = ‖z - a‖ * Real.exp (-L) := by
        dsimp [L]
        rw [Real.exp_neg, Real.exp_log (div_pos hr hR)]
        field_simp
      _ < ‖z - a‖ * Real.exp (L * w.re) := by
        gcongr
        nlinarith
  have hd : deriv g 0 = (z - a) * (L : ℂ) := by
    have h := ((hasDerivAt_id (0 : ℂ)).const_mul (L : ℂ)).cexp.const_mul (z - a)
    simpa [g] using (h.const_add a).deriv
  have hs := hp.density_schwarz hg.differentiableOn hgm
  rw [hg0, hd, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL] at hs
  exact (le_div_iff₀ (mul_pos hr hL)).mpr hs

end AreaDeficit
