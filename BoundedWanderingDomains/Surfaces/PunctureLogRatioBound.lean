/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CuspDensityBounds
import BoundedWanderingDomains.Surfaces.LogRatioBound

/-! # Logarithmic growth of a metric ratio at a new puncture -/

open Set Function Filter Metric
open scoped Manifold Topology

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

/-- The cusp upper bound for the new metric, together with a positive local
lower bound for the old metric, gives precisely the logarithmic growth used
by the cutoff/Riesz argument. -/
theorem chartLogRatio_le_const_sub_log_norm
    (p : DiscCover M) {U : TopologicalSpace.Opens M} (q : DiscCover U)
    (hU : Nonempty U) {d : OpenPartialHomeomorph M ℂ}
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {a z : ℂ} {R m : ℝ}
    (hball : ball a R \ {a} ⊆ (d.subtypeRestr hU).target)
    (hm : 0 < m) (hz : z ≠ a) (hzR : ‖z - a‖ < R)
    (hlog : 1 ≤ Real.log (R / ‖z - a‖))
    (hlower : m ≤ p.chartDensity d z) :
    p.chartLogRatio q hU d z ≤ Real.log (2 / m) - Real.log ‖z - a‖ := by
  have hr : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hzt : z ∈ (d.subtypeRestr hU).target :=
    hball ⟨by simpa only [mem_ball, dist_eq_norm] using hzR,
      by simpa only [mem_singleton_iff] using hz⟩
  have hq := q.chartDensity_upper_cusp
    (mdifferentiableOn_subtypeRestr hU hd)
    hball hz hzR
  have hden : 0 < ‖z - a‖ * Real.log (R / ‖z - a‖) :=
    mul_pos hr (lt_of_lt_of_le zero_lt_one hlog)
  have hq' : q.chartDensity (d.subtypeRestr hU) z ≤ 2 / ‖z - a‖ := by
    calc
      q.chartDensity (d.subtypeRestr hU) z ≤
          2 / (‖z - a‖ * Real.log (R / ‖z - a‖)) := hq
      _ ≤ 2 / ‖z - a‖ := by
        apply (div_le_div_iff_of_pos_left (by norm_num) hden hr).mpr
        nlinarith
  have hp : 0 < p.chartDensity d z :=
    p.chartDensity_pos hd (d.subtypeRestr_target_subset hU hzt)
  have hratio :
      p.densityRatio q ((d.subtypeRestr hU).symm z) ≤ (2 / m) / ‖z - a‖ := by
    have hxd := (d.subtypeRestr hU).map_target hzt
    have hx : (((d.subtypeRestr hU).symm z : U) : M) ∈ d.source := by
      simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage]
        using hxd
    rw [p.densityRatio_eq q hU hd hx]
    have heq : (((d.subtypeRestr hU).symm z : U) : M) = d.symm z :=
      d.subtypeRestr_symm_apply hU hzt
    rw [heq]
    apply (div_le_iff₀ hp).mpr
    calc
      q.density (d.subtypeRestr hU) ((d.subtypeRestr hU).symm z) ≤
          2 / ‖z - a‖ := hq'
      _ ≤ (2 / m) / ‖z - a‖ * p.chartDensity d z := by
        have hnonneg : 0 ≤ 2 / (m * ‖z - a‖) := by positivity
        have hmul := mul_le_mul_of_nonneg_left hlower hnonneg
        calc
          2 / ‖z - a‖ = (2 / (m * ‖z - a‖)) * m := by
            field_simp [ne_of_gt hm, ne_of_gt hr]
          _ ≤ (2 / (m * ‖z - a‖)) * p.chartDensity d z := hmul
          _ = (2 / m) / ‖z - a‖ * p.chartDensity d z := by ring
  rw [p.chartLogRatio_eq_log_densityRatio q hU hd hzt]
  calc
    Real.log (p.densityRatio q ((d.subtypeRestr hU).symm z)) ≤
        Real.log ((2 / m) / ‖z - a‖) :=
      Real.log_le_log
        (lt_of_lt_of_le zero_lt_one (p.one_le_densityRatio q _)) hratio
    _ = Real.log (2 / m) - Real.log ‖z - a‖ := by
      rw [Real.log_div (by positivity) (ne_of_gt hr)]

/-- Near a newly removed point the preceding lower bound is automatic for
the old metric.  Thus the logarithm of the metric quotient has coefficient
at most one in front of the logarithmic singularity. -/
theorem exists_chartLogRatio_le_const_sub_log_norm
    (p : DiscCover M) {U : TopologicalSpace.Opens M} (q : DiscCover U)
    (hU : Nonempty U) {d : OpenPartialHomeomorph M ℂ}
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {a : ℂ} (ha : a ∈ d.target) {R : ℝ} (hR : 0 < R)
    (hball : ball a R \ {a} ⊆ (d.subtypeRestr hU).target) :
    ∃ r > 0, r < R ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z ≠ a → ‖z - a‖ < r →
      p.chartLogRatio q hU d z ≤ C - Real.log ‖z - a‖ := by
  let m : ℝ := p.chartDensity d a / 2
  have hpa : 0 < p.chartDensity d a := p.chartDensity_pos hd ha
  have hm : 0 < m := by dsimp [m]; positivity
  have hnear : ∀ᶠ z in 𝓝 a, m < p.chartDensity d z :=
    (p.chartDensity_contDiffAt hd ha).continuousAt.eventually
      (eventually_gt_nhds (by dsimp [m]; linarith))
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff.mp hnear
  let r : ℝ := min δ (R / Real.exp 1)
  have hr : 0 < r := lt_min hδ (div_pos hR (Real.exp_pos 1))
  have hrR : r < R := (min_le_right δ _).trans_lt
    ((div_lt_iff₀ (Real.exp_pos 1)).mpr
      (lt_mul_of_one_lt_right hR (Real.one_lt_exp_iff.mpr zero_lt_one)))
  refine ⟨r, hr, hrR, max (Real.log (2 / m)) 0, le_max_right _ _, ?_⟩
  intro z hza hzr
  have hzrδ : ‖z - a‖ < δ := hzr.trans_le (min_le_left _ _)
  have hzrRexp : ‖z - a‖ < R / Real.exp 1 :=
    hzr.trans_le (min_le_right _ _)
  have hzrR : ‖z - a‖ < R := by
    have he : 1 ≤ Real.exp 1 := (Real.one_lt_exp_iff.mpr zero_lt_one).le
    have : R / Real.exp 1 ≤ R := (div_le_iff₀ (Real.exp_pos 1)).mpr (by
      nlinarith [Real.exp_pos 1])
    exact hzrRexp.trans_le this
  have hnorm : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hza)
  have hquot : Real.exp 1 ≤ R / ‖z - a‖ := by
    apply (le_div_iff₀ hnorm).mpr
    simpa only [mul_comm] using
      ((lt_div_iff₀ (Real.exp_pos 1)).mp hzrRexp).le
  have hlog : 1 ≤ Real.log (R / ‖z - a‖) := by
    rw [Real.le_log_iff_exp_le (div_pos hR hnorm)]
    exact hquot
  exact (p.chartLogRatio_le_const_sub_log_norm q hU hd hball hm hza hzrR hlog
    (hδball (by simpa only [mem_ball, dist_eq_norm] using hzrδ)).le).trans
      (sub_le_sub_right (le_max_left _ _) _)

end AreaDeficit.Surfaces.DiscCover

#print axioms AreaDeficit.Surfaces.DiscCover.chartLogRatio_le_const_sub_log_norm
#print axioms AreaDeficit.Surfaces.DiscCover.exists_chartLogRatio_le_const_sub_log_norm
