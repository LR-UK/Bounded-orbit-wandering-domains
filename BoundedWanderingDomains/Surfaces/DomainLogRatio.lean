/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DomainRemoteBound
import BoundedWanderingDomains.Surfaces.DomainAreaGain

/-! # Logarithmic density ratios for nested ambient domains -/

open Set Function Filter Metric MeasureTheory
open scoped Manifold Topology ENNReal ContDiff

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]

/-- Intrinsic logarithmic quotient of the componentwise domain densities. -/
noncomputable def domainLogRatio (p : DiscCover M)
    (U V : TopologicalSpace.Opens M) (x : M) : ℝ :=
  Real.log (p.domainDensityRatio V x) -
    Real.log (p.domainDensityRatio U x)

theorem domainLogRatio_measurable (p : DiscCover M)
    [MeasurableSpace M] [BorelSpace M]
    (U V : TopologicalSpace.Opens M) :
    Measurable (p.domainLogRatio U V) :=
  (p.domainDensityRatio_measurable V).log.sub
    (p.domainDensityRatio_measurable U).log

/-- The logarithm of the quotient of the componentwise hyperbolic densities
of two ambient open domains. -/
noncomputable def domainChartLogRatio (p : DiscCover M)
    (U V : TopologicalSpace.Opens M) (c : OpenPartialHomeomorph M ℂ) : ℂ → ℝ :=
  fun z => Real.log (p.domainChartDensity V c z) -
    Real.log (p.domainChartDensity U c z)

theorem domainLogRatio_eq_chart (p : DiscCover M)
    {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {x : M} (hx : x ∈ V) (hxc : x ∈ c.source) :
    p.domainLogRatio U V x = p.domainChartLogRatio U V c (c x) := by
  have hV : 0 < p.domainChartDensity V c (c x) :=
    p.domainChartDensity_pos V hc ⟨c.map_source hxc, by
      change c.symm (c x) ∈ V
      rw [c.left_inv hxc]
      exact hx⟩
  have hU : 0 < p.domainChartDensity U c (c x) :=
    p.domainChartDensity_pos U hc ⟨c.map_source hxc, by
      change c.symm (c x) ∈ U
      rw [c.left_inv hxc]
      exact hVU hx⟩
  have hp : 0 < p.chartDensity c (c x) :=
    p.chartDensity_pos hc (c.map_source hxc)
  rw [domainLogRatio, domainChartLogRatio,
    p.domainDensityRatio_chart V hc hxc,
    p.domainDensityRatio_chart U hc hxc,
    Real.log_div hV.ne' hp.ne', Real.log_div hU.ne' hp.ne']
  ring

theorem domainChartLogRatio_nonneg (p : DiscCover M)
    {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {z : ℂ} (hz : z ∈ domainChartSet V c) :
    0 ≤ p.domainChartLogRatio U V c z := by
  exact sub_nonneg.mpr (Real.log_le_log
    (p.domainChartDensity_pos U hc ⟨hz.1, hVU hz.2⟩)
    (p.domainChartDensity_mono hVU hc hz))

theorem domainChartLogRatio_contDiffAt (p : DiscCover M)
    {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {z : ℂ} (hz : z ∈ domainChartSet V c) :
    ContDiffAt ℝ 2 (p.domainChartLogRatio U V c) z := by
  have hV := p.domainChartDensity_contDiffAt V hc hz
  have hU := p.domainChartDensity_contDiffAt U hc ⟨hz.1, hVU hz.2⟩
  exact (hV.log (ne_of_gt (p.domainChartDensity_pos V hc hz))).sub
    (hU.log (ne_of_gt (p.domainChartDensity_pos U hc ⟨hz.1, hVU hz.2⟩)))

theorem domainLogRatio_continuousAt (p : DiscCover M)
    {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    {x : M} (hx : x ∈ V) :
    ContinuousAt (p.domainLogRatio U V) x := by
  let c := chartAt ℂ x
  have hxs : x ∈ c.source := mem_chart_source ℂ x
  have hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source :=
    (mdifferentiable_chart (I := 𝓘(ℂ)) x).1
  have hzt : c x ∈ domainChartSet V c := by
    refine ⟨c.map_source hxs, ?_⟩
    change c.symm (c x) ∈ V
    rw [c.left_inv hxs]
    exact hx
  have hright : ContinuousAt
      (fun y => p.domainChartLogRatio U V c (c y)) x :=
    (p.domainChartLogRatio_contDiffAt hVU hc hzt).continuousAt.comp
      (c.continuousAt hxs)
  apply hright.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hxs, V.isOpen.mem_nhds hx] with y hys hyV
  exact p.domainLogRatio_eq_chart hVU hc hyV hys

theorem domainChartLogRatio_laplacian (p : DiscCover M)
    {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {z : ℂ} (hz : z ∈ domainChartSet V c) :
    Laplacian.laplacian (p.domainChartLogRatio U V c) z =
      (p.domainChartDensity V c z)^2 -
        (p.domainChartDensity U c z)^2 := by
  have hV := (p.domainChartDensity_contDiffAt V hc hz).log
    (ne_of_gt (p.domainChartDensity_pos V hc hz))
  have hU := (p.domainChartDensity_contDiffAt U hc ⟨hz.1, hVU hz.2⟩).log
    (ne_of_gt (p.domainChartDensity_pos U hc ⟨hz.1, hVU hz.2⟩))
  change Laplacian.laplacian
    ((fun t => Real.log (p.domainChartDensity V c t)) -
      (fun t => Real.log (p.domainChartDensity U c t))) z = _
  rw [hV.laplacian_sub hU, p.domainChartDensity_curvature V hc hz,
    p.domainChartDensity_curvature U hc ⟨hz.1, hVU hz.2⟩]

theorem domainChartLogRatio_laplacian_nonneg (p : DiscCover M)
    {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {z : ℂ} (hz : z ∈ domainChartSet V c) :
    0 ≤ Laplacian.laplacian (p.domainChartLogRatio U V c) z := by
  rw [p.domainChartLogRatio_laplacian hVU hc hz]
  have hmono := p.domainChartDensity_mono hVU hc hz
  have hU := p.domainChartDensity_pos U hc ⟨hz.1, hVU hz.2⟩
  have hV := p.domainChartDensity_pos V hc hz
  nlinarith

end AreaDeficit.Surfaces.DiscCover

#print axioms AreaDeficit.Surfaces.DiscCover.domainChartLogRatio_laplacian
