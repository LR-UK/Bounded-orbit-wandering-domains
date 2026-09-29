module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SubdomainDensity

@[expose] public section
open Set Function Filter Metric MeasureTheory
open scoped Manifold Topology ENNReal ContDiff
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]
noncomputable def chartLogRatio (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (hU : Nonempty U) (c : OpenPartialHomeomorph M ℂ) : ℂ → ℝ :=
  fun z => Real.log (q.chartDensity (c.subtypeRestr hU) z) - Real.log (p.chartDensity c z)
theorem chartLogRatio_nonneg (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (hU : Nonempty U) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {z : ℂ} (hz : z ∈ (c.subtypeRestr hU).target) :
    0 ≤ p.chartLogRatio q hU c z := by
  exact sub_nonneg.mpr (Real.log_le_log
    (p.chartDensity_pos hc (c.subtypeRestr_target_subset hU hz))
    (p.chartDensity_subdomain_le q hU hc hz))
theorem chartLogRatio_contDiffAt (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (hU : Nonempty U) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {z : ℂ} (hz : z ∈ (c.subtypeRestr hU).target) :
    ContDiffAt ℝ 2 (p.chartLogRatio q hU c) z := by
  have hd := mdifferentiableOn_subtypeRestr hU hc
  have hz' := c.subtypeRestr_target_subset hU hz
  exact ((q.chartDensity_contDiffAt hd hz).log (ne_of_gt (q.chartDensity_pos hd hz))).sub
    ((p.chartDensity_contDiffAt hc hz').log (ne_of_gt (p.chartDensity_pos hc hz')))
theorem chartLogRatio_laplacian (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (hU : Nonempty U) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {z : ℂ} (hz : z ∈ (c.subtypeRestr hU).target) :
    Laplacian.laplacian (p.chartLogRatio q hU c) z =
      (q.chartDensity (c.subtypeRestr hU) z)^2 - (p.chartDensity c z)^2 := by
  have hd := mdifferentiableOn_subtypeRestr hU hc
  have hz' := c.subtypeRestr_target_subset hU hz
  have hq := (q.chartDensity_contDiffAt hd hz).log (ne_of_gt (q.chartDensity_pos hd hz))
  have hp := (p.chartDensity_contDiffAt hc hz').log (ne_of_gt (p.chartDensity_pos hc hz'))
  change Laplacian.laplacian
    ((fun t => Real.log (q.chartDensity (c.subtypeRestr hU) t)) -
      (fun t => Real.log (p.chartDensity c t))) z = _
  rw [hq.laplacian_sub hp,q.chartDensity_curvature hd hz,
    p.chartDensity_curvature hc hz']
theorem chartLogRatio_laplacian_nonneg (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (hU : Nonempty U) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {z : ℂ} (hz : z ∈ (c.subtypeRestr hU).target) :
    0 ≤ Laplacian.laplacian (p.chartLogRatio q hU c) z := by
  rw [p.chartLogRatio_laplacian q hU hc hz]
  have hp := p.chartDensity_pos hc (c.subtypeRestr_target_subset hU hz)
  have hle := p.chartDensity_subdomain_le q hU hc hz
  nlinarith
end AreaDeficit.Surfaces.DiscCover
