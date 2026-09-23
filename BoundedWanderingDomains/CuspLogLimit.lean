/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.CuspAffineBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Set Filter Metric
open scoped Topology

namespace AreaDeficit

theorem tendsto_log_add_div_atTop (C : ℝ) :
    Tendsto (fun t : ℝ => Real.log (C + t) / t) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-C) 1 one_ne_zero).comp
    (tendsto_atTop_add_const_left atTop C tendsto_id)
  simpa [Function.comp_def, add_comm C] using h

/-- Multiplicative cusp bounds determine the leading logarithmic coefficient. -/
theorem tendsto_log_of_cusp_bounds {ι : Type*} {l : Filter ι} {t q : ι → ℝ}
    {C D : ℝ} (ht : Tendsto t l atTop)
    (hq : ∀ᶠ x in l, 0 < q x)
    (hl : ∀ᶠ x in l, 1 / (4 * (C + t x)) ≤ q x)
    (hu : ∀ᶠ x in l, q x ≤ 2 / (D + t x)) :
    Tendsto (fun x => Real.log (q x) / t x) l (𝓝 0) := by
  have hc : Tendsto (fun x => Real.log (C + t x) / t x) l (𝓝 0) :=
    (tendsto_log_add_div_atTop C).comp ht
  have hd : Tendsto (fun x => Real.log (D + t x) / t x) l (𝓝 0) :=
    (tendsto_log_add_div_atTop D).comp ht
  have h4 : Tendsto (fun x => Real.log 4 / t x) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop ht
  have h2 : Tendsto (fun x => Real.log 2 / t x) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop ht
  have hlo : Tendsto (fun x => (-Real.log 4 - Real.log (C + t x)) / t x) l (𝓝 0) := by
    simpa only [sub_div, neg_div, neg_zero, sub_zero] using h4.neg.sub hc
  have hup : Tendsto (fun x => (Real.log 2 - Real.log (D + t x)) / t x) l (𝓝 0) := by
    simpa only [sub_div, sub_zero] using h2.sub hd
  apply hlo.squeeze' hup
  · filter_upwards [hl, hq, ht.eventually_gt_atTop (max 0 (-C))] with x hx hqx htx
    have htp : 0 < t x := (le_max_left _ _).trans_lt htx
    have hcp : 0 < C + t x := by have := (le_max_right 0 (-C)).trans_lt htx; linarith
    apply (div_le_div_iff_of_pos_right htp).mpr
    have hh := Real.log_le_log (by positivity : 0 < 1 / (4 * (C + t x))) hx
    simp [Real.log_mul, hcp.ne', show (4 : ℝ) ≠ 0 by norm_num] at hh
    linarith
  · filter_upwards [hu, hq, ht.eventually_gt_atTop (max 0 (-D))] with x hx hqx htx
    have htp : 0 < t x := (le_max_left _ _).trans_lt htx
    have hdp : 0 < D + t x := by have := (le_max_right 0 (-D)).trans_lt htx; linarith
    apply (div_le_div_iff_of_pos_right htp).mpr
    have hh := Real.log_le_log hqx hx
    simpa [Real.log_div, hdp.ne', show (2 : ℝ) ≠ 0 by norm_num] using hh

end AreaDeficit
