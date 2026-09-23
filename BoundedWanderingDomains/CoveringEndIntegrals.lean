/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.CutoffEndLimits

open Set Filter MeasureTheory InnerProductSpace Laplacian Metric
open scoped Topology ContDiff

namespace AreaDeficit

theorem IsHolomorphicDiscCovering.log_density_contDiffAt {p : ℂ → ℂ} {S : Set ℂ}
    (hp : IsHolomorphicDiscCovering p S) {z : ℂ} (hz : z ∈ S) :
    ContDiffAt ℝ 2 (fun w => Real.log (coveringDensity p w)) z :=
  (hp.density_contDiffAt hz).log (hp.density_pos hz).ne'

theorem IsHolomorphicDiscCovering.integrable_finite_end {p : ℂ → ℂ} {S : Set ℂ}
    (hp : IsHolomorphicDiscCovering p S) {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : ball a R \ {a} ⊆ S) :
    ∀ᶠ t : ℝ in atTop, Integrable (fun z : ℂ =>
      Real.log (coveringDensity p z) * Δ (logCutoff a (-2*t) (-t)) z) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  filter_upwards [eventually_gt_atTop (0 : ℝ), he.eventually (eventually_lt_nhds hR)] with t ht hte
  apply integrable_mul_laplacian_logCutoff a (by linarith)
  intro z hzA hzB
  have hza : z ≠ a := by
    intro hz
    have hrp := Real.exp_pos (-2*t)
    simp only [hz, sub_self, norm_zero] at hzA
    linarith
  exact (hp.log_density_contDiffAt (hball ⟨mem_ball_iff_norm.mpr (hzB.trans_lt hte), hza⟩)).continuousAt

theorem IsHolomorphicDiscCovering.integrable_infinite_end {p : ℂ → ℂ} {S : Set ℂ}
    (hp : IsHolomorphicDiscCovering p S) {a : ℂ} {R : ℝ}
    (hout : {w : ℂ | R < ‖w - a‖} ⊆ S) :
    ∀ᶠ t : ℝ in atTop, Integrable (fun z : ℂ =>
      Real.log (coveringDensity p z) * Δ (logCutoff a t (2*t)) z) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), Real.tendsto_exp_atTop.eventually_gt_atTop R]
    with t ht hte
  apply integrable_mul_laplacian_logCutoff a (by linarith)
  intro z hzA _
  exact (hp.log_density_contDiffAt (hout (hte.trans_le hzA))).continuousAt

/-- Each finite puncture contributes minus `2π` before the inner cutoff is subtracted. -/
theorem IsHolomorphicDiscCovering.integral_finite_end {p : ℂ → ℂ} {S : Set ℂ}
    (hp : IsHolomorphicDiscCovering p S) {a b : ℂ} (hab : a ≠ b)
    (ha : a ∉ S) (hb : b ∉ S) {R : ℝ} (hR : 0 < R)
    (hball : ball a R \ {a} ⊆ S) :
    Tendsto (fun t : ℝ => ∫ z : ℂ,
      Real.log (coveringDensity p z) * Δ (logCutoff a (-2*t) (-t)) z)
      atTop (𝓝 (-2 * Real.pi)) :=
  tendsto_integral_finite_end a (hp.log_density_finite_cusp hab ha hb hR hball)
    (hp.integrable_finite_end hR hball)

/-- The expanding outer cutoff contributes minus `2π`. -/
theorem IsHolomorphicDiscCovering.integral_infinite_end {p : ℂ → ℂ} {S : Set ℂ}
    (hp : IsHolomorphicDiscCovering p S) {a b : ℂ} (hab : a ≠ b)
    (ha : a ∉ S) (hb : b ∉ S) {R : ℝ} (hR : 0 < R)
    (hout : {w : ℂ | R < ‖w - a‖} ⊆ S) :
    Tendsto (fun t : ℝ => ∫ z : ℂ,
      Real.log (coveringDensity p z) * Δ (logCutoff a t (2*t)) z)
      atTop (𝓝 (-2 * Real.pi)) := by
  apply tendsto_integral_infinite_end a
    (hp.log_density_infinite_cusp hab ha hb hR hout ?_) (hp.integrable_infinite_end hout)
  simpa only [dist_eq_norm] using tendsto_dist_right_cocompact_atTop a

end AreaDeficit
