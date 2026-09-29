module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.RemoteDensityBound
public import BoundedWanderingDomains.Surfaces.ChartGainCutoff

@[expose] public section
open Set Function Filter Metric MeasureTheory Laplacian
open scoped Manifold Topology ENNReal ContDiff
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

theorem chartLogRatio_eq_log_densityRatio (p : DiscCover M)
    {U : TopologicalSpace.Opens M} (q : DiscCover U) (hU : Nonempty U)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {z : ℂ} (hz : z ∈ (c.subtypeRestr hU).target) :
    p.chartLogRatio q hU c z = Real.log (p.densityRatio q ((c.subtypeRestr hU).symm z)) := by
  let d := c.subtypeRestr hU
  have hxd := d.map_target hz
  have hx : (d.symm z : M) ∈ c.source := by
    simpa only [d,OpenPartialHomeomorph.subtypeRestr_source,mem_preimage] using hxd
  rw [p.densityRatio_eq q hU hc hx,Real.log_div
    (ne_of_gt (q.density_pos (mdifferentiableOn_subtypeRestr hU hc) hxd))
    (ne_of_gt (p.density_pos hc hx))]
  unfold chartLogRatio chartDensity
  rw [show (d.symm z : M) = c.symm z from c.subtypeRestr_symm_apply hU hz]

/-- Converts a geometric ratio bound to the analytic bound used in Green's identity. -/
theorem chartLogRatio_le_of_densityRatio_le (p : DiscCover M)
    {U : TopologicalSpace.Opens M} (q : DiscCover U) (hU : Nonempty U)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {z : ℂ} (hz : z ∈ (c.subtypeRestr hU).target) {B : ℝ}
    (hB : p.densityRatio q ((c.subtypeRestr hU).symm z) ≤ B) :
    p.chartLogRatio q hU c z ≤ Real.log B := by
  rw [p.chartLogRatio_eq_log_densityRatio q hU hc hz]
  exact Real.log_le_log (lt_of_lt_of_le zero_lt_one (p.one_le_densityRatio q _)) hB

/-- A cutoff bound whose only metric bound is the intrinsic density ratio. -/
theorem chart_gain_cutoff_of_ratio (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (hU : Nonempty U) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {V : Set ℂ} (hV : IsOpen V) (hVc : V ⊆ (c.subtypeRestr hU).target)
    {chi : ℂ → ℝ} {B : ℝ} (hB : 1 ≤ B)
    (hchi : ContDiff ℝ 2 chi) (hcomp : HasCompactSupport chi)
    (hchi0 : ∀ z, 0 ≤ chi z) (hsupp : tsupport chi ⊆ V)
    (hbound : ∀ z ∈ V, p.densityRatio q ((c.subtypeRestr hU).symm z) ≤ B) :
    (∫⁻ z, ENNReal.ofReal (chi z *
      ((q.chartDensity (c.subtypeRestr hU) z)^2 - (p.chartDensity c z)^2))) ≤
      ENNReal.ofReal (Real.log B * ∫ z, |Δ chi z|) := by
  exact p.chart_gain_cutoff q hU hc hV hVc (Real.log_nonneg hB) hchi hcomp hchi0 hsupp
    (fun z hz => p.chartLogRatio_le_of_densityRatio_le q hU hc (hVc hz) (hbound z hz))
end AreaDeficit.Surfaces.DiscCover
