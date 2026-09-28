/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.LogGrowthCutoff
import BoundedWanderingDomains.Surfaces.DiscComparisonInfinity
import BoundedWanderingDomains.Surfaces.LogRatioBound

/-! # Vanishing boundary mass at an old puncture -/

open Set Function Filter Metric MeasureTheory Laplacian
open scoped Manifold Topology

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]

omit [T2Space M] [SecondCountableTopology M] in
/-- At an old end, a chart parametrization which escapes every compact subset
of the old surface sees the logarithmic metric quotient tend to zero.
Consequently its Riesz boundary contribution vanishes. -/
theorem tendsto_old_puncture_boundary_mass_zero
    (p : DiscCover M) {K : Set M} (hK : IsCompact K)
    {U : TopologicalSpace.Opens M} (hU : ∀ y : M, y ∈ U ↔ y ∉ K)
    (q : DiscCover U) {d : OpenPartialHomeomorph M ℂ}
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {a : ℂ} (x : ℂ → U)
    (hx : Tendsto (fun z => (x z : M)) (𝓝[≠] a) (cocompact M))
    (hcoord : ∀ᶠ z in 𝓝[≠] a,
      z ∈ (d.subtypeRestr (show Nonempty U from ⟨x a⟩)).target ∧
        x z = (d.subtypeRestr (show Nonempty U from ⟨x a⟩)).symm z) :
    Tendsto (fun t : ℝ => ∫ z : ℂ,
      p.chartLogRatio q (show Nonempty U from ⟨x a⟩) d z *
        Δ (AreaDeficit.logCutoff a (-2 * t) (-t)) z)
      atTop (𝓝 0) := by
  let hUN : Nonempty U := ⟨x a⟩
  have hlog := p.log_densityRatio_tendsto_zero_of_tendsto_cocompact
    hK hU q x hx
  have hzero : Tendsto (p.chartLogRatio q hUN d) (𝓝[≠] a) (𝓝 0) := by
    apply hlog.congr'
    filter_upwards [hcoord] with z hz
    rw [p.chartLogRatio_eq_log_densityRatio q hUN hd hz.1]
    congr 2
    exact hz.2
  exact AreaDeficit.tendsto_integral_mul_laplacian_logCutoff_zero a hzero

end AreaDeficit.Surfaces.DiscCover
