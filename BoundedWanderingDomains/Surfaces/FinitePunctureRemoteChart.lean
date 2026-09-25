/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.FinitePunctureChartCutoff
import BoundedWanderingDomains.Surfaces.RemoteDensityBound

/-! # A remote gain estimate with a fixed cutoff through finite punctures

The logarithmic bound depends only on ambient compact separation. The finite
exceptional set may vary independently of the cutoff. -/

open Set Function Filter Metric MeasureTheory Laplacian
open scoped Manifold Topology ENNReal ContDiff
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

theorem remote_chart_gain_finite_punctures (p : DiscCover M) {K C : Set M}
    (hK : IsClosed K) (hC : IsCompact C) (hCK : Disjoint C K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (U : TopologicalSpace.Opens M) (r : DiscCover U)
      (W : TopologicalSpace.Opens U) (s : DiscCover W)
      (_hW : ∀ x : U, x ∈ W ↔ (x : M) ∉ K)
      (hNE : Nonempty W) (c : OpenPartialHomeomorph U ℂ),
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source →
      ∀ (F : Finset ℂ) (D : Set ℂ), IsOpen D →
      (∀ z ∈ D, z ∉ F → z ∈ (c.subtypeRestr hNE).target) →
      (∀ z ∈ D, z ∉ F → (((c.subtypeRestr hNE).symm z : U) : M) ∈ C) →
      ∀ chi : ℂ → ℝ, ContDiff ℝ 2 chi → HasCompactSupport chi →
      (∀ z, 0 ≤ chi z) → tsupport chi ⊆ D →
      (∫⁻ z, ENNReal.ofReal (chi z *
        (if z ∈ F then 0 else
          (s.chartDensity (c.subtypeRestr hNE) z)^2 - (r.chartDensity c z)^2))) ≤
        ENNReal.ofReal (B * ∫ z, |Δ chi z|) := by
  obtain ⟨A, hA, hbound⟩ := p.remote_densityRatio_bound hK hC hCK
  refine ⟨Real.log A, Real.log_nonneg hA, ?_⟩
  intro U r W s hW hNE c hc F D hD htarget hDC chi hchi hcomp hchi0 hsupp
  exact r.chart_gain_cutoff_finite_exceptions s hNE hc F hD htarget
    (Real.log_nonneg hA) hchi hcomp hchi0 hsupp
    (fun z hz hf => r.chartLogRatio_le_of_densityRatio_le s hNE hc
      (htarget z hz hf) (hbound U r W s hW _ (hDC z hz hf)))

end AreaDeficit.Surfaces.DiscCover
