module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.Surfaces.DensityRatioInvariance

@[expose] public section

/-! # Continuity of the intrinsic metric ratio -/
open Set Function Filter Metric MeasureTheory
open scoped Manifold Topology ENNReal
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

theorem densityRatio_continuous (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) : Continuous (p.densityRatio q) := by
  rw [continuous_iff_continuousAt]
  intro x
  let c := chartAt ℂ (x : M)
  let hU : Nonempty U := ⟨x⟩
  let d := c.subtypeRestr hU
  have hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source := fun z hz =>
    (mdifferentiableAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas _) hz).mdifferentiableWithinAt
  have hd := mdifferentiableOn_subtypeRestr hU hc
  have hx : (x : M) ∈ c.source := mem_chart_source ℂ (x : M)
  have hxd : x ∈ d.source := by
    simpa only [d,OpenPartialHomeomorph.subtypeRestr_source,mem_preimage] using hx
  have hpc : ContinuousAt (fun y : U => p.chartDensity c (c y)) x :=
    ((p.chartDensity_contDiffAt hc (c.map_source hx)).continuousAt.comp
      (c.continuousAt hx)).comp continuous_subtype_val.continuousAt
  have hqc := (q.chartDensity_contDiffAt hd (d.map_source hxd)).continuousAt.comp
    (d.continuousAt hxd)
  have hpn : p.chartDensity c (c x) ≠ 0 := ne_of_gt (p.chartDensity_pos hc (c.map_source hx))
  apply (hqc.div hpc hpn).congr_of_eventuallyEq
  filter_upwards [d.open_source.mem_nhds hxd] with y hy
  have hyc : (y : M) ∈ c.source := by
    simpa only [d,OpenPartialHomeomorph.subtypeRestr_source,mem_preimage] using hy
  rw [p.densityRatio_eq q hU hc hyc]
  change q.density d y / p.density c y =
    q.density d (d.symm (d y)) / p.density c (c.symm (c y))
  rw [d.left_inv hy,c.left_inv hyc]

theorem densityRatio_measurable [MeasurableSpace M] [BorelSpace M]
    (p : DiscCover M) {U : TopologicalSpace.Opens M} (q : DiscCover U) :
    Measurable (p.densityRatio q) := (p.densityRatio_continuous q).measurable

end AreaDeficit.Surfaces.DiscCover
