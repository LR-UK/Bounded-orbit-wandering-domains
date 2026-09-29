module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.LogRadialIntegral
public import BoundedWanderingDomains.CuspDensityBounds
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-! # Integrability of the model cusp area kernel -/

open Set MeasureTheory Metric
open scoped ENNReal

namespace AreaDeficit

theorem integrable_truncated_inverse_square (b c : ℝ) (hc : 0 < c) :
    Integrable (fun t : ℝ => if t < b - c then (b - t) ^ (-2 : ℝ) else 0) := by
  have hpow : IntegrableOn (fun u : ℝ => u ^ (-2 : ℝ)) (Ioi c) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hc
  have hind : Integrable
      ((Ioi c).indicator (fun u : ℝ => u ^ (-2 : ℝ))) :=
    hpow.integrable_indicator measurableSet_Ioi
  have hmove := hind.comp_neg.comp_add_right (-b)
  apply hmove.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Set.indicator, mem_Ioi]
  have he : c < -(t + -b) ↔ t < b - c := by constructor <;> intro h <;> linarith
  simp only [he]
  split_ifs
  · congr 1; ring
  · rfl

/-- The squared logarithmic cusp majorant is integrable on a smaller
punctured disc.  This is the analytic input needed to turn the pointwise
cusp-density estimate into finite hyperbolic area near an isolated end. -/
theorem integrable_cusp_area_kernel {R : ℝ} (hR : 0 < R) :
    Integrable (fun z : ℂ =>
      if z ≠ 0 ∧ ‖z‖ < R / 2 then
        (Real.log R - Real.log ‖z‖) ^ (-2 : ℝ) / ‖z‖ ^ 2
      else 0) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hf := integrable_truncated_inverse_square
    (Real.log R) (Real.log 2) hlog2
  have hrad := integrable_log_radial hf
  apply hrad.congr (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z = 0
  · simp [hz]
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hR2 : 0 < R / 2 := by positivity
  have hlogdiv : Real.log (R / 2) = Real.log R - Real.log 2 := by
    rw [Real.log_div hR.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  have he : Real.log ‖z‖ < Real.log R - Real.log 2 ↔ ‖z‖ < R / 2 := by
    rw [← hlogdiv]
    exact Real.strictMonoOn_log.lt_iff_lt hzn hR2
  simp only [he]
  split_ifs <;> simp_all

/-- Equivalent form matching the upper bound for a covering density. -/
theorem integrable_cusp_density_sq_majorant {R : ℝ} (hR : 0 < R) :
    Integrable (fun z : ℂ =>
      if z ≠ 0 ∧ ‖z‖ < R / 2 then
        1 / (‖z‖ * Real.log (R / ‖z‖)) ^ 2
      else 0) := by
  apply (integrable_cusp_area_kernel hR).congr
    (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z = 0
  · simp [hz]
  by_cases hzR : ‖z‖ < R / 2
  · have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hzr : ‖z‖ < R := hzR.trans (by linarith)
    have hd : 0 < Real.log R - Real.log ‖z‖ := by
      rw [← Real.log_div hR.ne' hzn.ne']
      exact Real.log_pos ((one_lt_div hzn).mpr hzr)
    have hcond : z ≠ 0 ∧ ‖z‖ < R / 2 := ⟨hz, hzR⟩
    simp only [hcond]
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
      Real.rpow_neg hd.le, Real.rpow_two,
      Real.log_div hR.ne' hzn.ne']
    field_simp
  · simp [hz, hzR]

/-- Translation does not affect integrability of the cusp majorant. -/
theorem integrable_cusp_density_sq_majorant_at (a : ℂ) {R : ℝ} (hR : 0 < R) :
    Integrable (fun z : ℂ =>
      if z ≠ a ∧ ‖z - a‖ < R / 2 then
        1 / (‖z - a‖ * Real.log (R / ‖z - a‖)) ^ 2
      else 0) := by
  have h := (integrable_cusp_density_sq_majorant hR).comp_sub_right a
  convert h using 1
  funext z
  simp only [sub_ne_zero]

/-- A disc-covering metric has finite area in a sufficiently small
neighbourhood of every isolated puncture. -/
theorem IsHolomorphicDiscCovering.integrableOn_density_sq_cusp
    {p : ℂ → ℂ} {S : Set ℂ} (hp : IsHolomorphicDiscCovering p S)
    {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : ball a R \ {a} ⊆ S) :
    IntegrableOn (fun z => (coveringDensity p z) ^ 2)
      (ball a (R / 2) \ {a}) := by
  let B : Set ℂ := ball a (R / 2) \ {a}
  let g : ℂ → ℝ := fun z =>
    4 * if z ≠ a ∧ ‖z - a‖ < R / 2 then
      1 / (‖z - a‖ * Real.log (R / ‖z - a‖)) ^ 2
    else 0
  have hg : Integrable g :=
    (integrable_cusp_density_sq_majorant_at a hR).const_mul 4
  have hBmeas : MeasurableSet B :=
    measurableSet_ball.diff (measurableSet_singleton a)
  have hcont : ContinuousOn (fun z => (coveringDensity p z) ^ 2) B := by
    intro z hz
    have hzR2 : ‖z - a‖ < R / 2 := by
      simpa only [mem_ball, dist_eq_norm] using hz.1
    have hzR : ‖z - a‖ < R := hzR2.trans (by linarith)
    have hza : z ≠ a := by simpa only [mem_singleton_iff] using hz.2
    exact ((hp.density_contDiffAt (hball ⟨by
      simpa only [mem_ball, dist_eq_norm] using hzR, by
      simpa only [mem_singleton_iff] using hza⟩)).continuousAt.pow 2).continuousWithinAt
  apply Integrable.mono' hg.integrableOn
    (hcont.aestronglyMeasurable hBmeas)
  filter_upwards [ae_restrict_mem hBmeas] with z hz
  have hzR2 : ‖z - a‖ < R / 2 := by
    simpa only [B, mem_sdiff, mem_ball, dist_eq_norm, mem_singleton_iff] using hz.1
  have hzR : ‖z - a‖ < R := hzR2.trans (by linarith)
  have hza : z ≠ a := by
    simpa only [B, mem_sdiff, mem_ball, dist_eq_norm, mem_singleton_iff] using hz.2
  have hzs : z ∈ S := hball ⟨by
    simpa only [mem_ball, dist_eq_norm] using hzR, by
    simpa only [mem_singleton_iff] using hza⟩
  have hr : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hza)
  have hl : 0 < Real.log (R / ‖z - a‖) :=
    Real.log_pos ((one_lt_div hr).mpr hzR)
  have hd : 0 < ‖z - a‖ * Real.log (R / ‖z - a‖) := mul_pos hr hl
  have hu := hp.density_upper_cusp hball hza hzR
  have hpos := hp.density_pos hzs
  change ‖(coveringDensity p z) ^ 2‖ ≤ g z
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hcond : z ≠ a ∧ ‖z - a‖ < R / 2 := ⟨hza, hzR2⟩
  dsimp only [g]
  rw [ite_eq_left hcond]
  have hupper_nonneg : 0 ≤ 2 / (‖z - a‖ * Real.log (R / ‖z - a‖)) :=
    div_nonneg (by norm_num) hd.le
  have hsquare : (coveringDensity p z) ^ 2 ≤
      (2 / (‖z - a‖ * Real.log (R / ‖z - a‖))) ^ 2 := by
    nlinarith
  calc
    (coveringDensity p z) ^ 2 ≤
        (2 / (‖z - a‖ * Real.log (R / ‖z - a‖))) ^ 2 := hsquare
    _ = 4 * (1 / (‖z - a‖ * Real.log (R / ‖z - a‖)) ^ 2) := by ring

/-- Consequently the curvature-minus-one area of the smaller cusp disc is
finite. -/
theorem IsHolomorphicDiscCovering.lintegral_density_sq_cusp_lt_top
    {p : ℂ → ℂ} {S : Set ℂ} (hp : IsHolomorphicDiscCovering p S)
    {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : ball a R \ {a} ⊆ S) :
    (∫⁻ z in ball a (R / 2) \ {a},
      ENNReal.ofReal ((coveringDensity p z) ^ 2)) < ⊤ := by
  have hi := hp.integrableOn_density_sq_cusp hR hball
  exact lt_top_iff_ne_top.mpr
    ((lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
      (ae_of_all _ (fun _ => sq_nonneg _))).mpr hi)

end AreaDeficit
