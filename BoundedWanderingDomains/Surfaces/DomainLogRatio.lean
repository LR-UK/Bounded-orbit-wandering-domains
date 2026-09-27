/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DomainRemoteBound

/-! # Logarithmic density ratios for nested ambient domains -/

open Set Function Filter Metric MeasureTheory
open scoped Manifold Topology ENNReal ContDiff

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]

/-- The logarithm of the quotient of the componentwise hyperbolic densities
of two ambient open domains. -/
noncomputable def domainChartLogRatio (p : DiscCover M)
    (U V : TopologicalSpace.Opens M) (c : OpenPartialHomeomorph M ℂ) : ℂ → ℝ :=
  fun z => Real.log (p.domainChartDensity V c z) -
    Real.log (p.domainChartDensity U c z)

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
