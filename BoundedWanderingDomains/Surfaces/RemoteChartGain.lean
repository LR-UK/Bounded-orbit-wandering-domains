module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.LogRatioBound

@[expose] public section
open Set Function Filter Metric MeasureTheory Laplacian
open scoped Manifold Topology ENNReal ContDiff
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

/-- The analytic chart bound with its constant derived solely from ambient compact
separation. This is the chart estimate, not the full noncompact area theorem. -/
theorem remote_chart_gain_bound (p : DiscCover M) {K C : Set M}
    (hK : IsClosed K) (hC : IsCompact C) (hCK : Disjoint C K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (V : TopologicalSpace.Opens M) (q : DiscCover V)
      (W : TopologicalSpace.Opens V) (s : DiscCover W)
      (_hW : ∀ x : V, x ∈ W ↔ (x : M) ∉ K)
      (hNE : Nonempty W) (c : OpenPartialHomeomorph V ℂ),
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source →
      ∀ (D : Set ℂ), IsOpen D → D ⊆ (c.subtypeRestr hNE).target →
      (∀ z ∈ D, (((c.subtypeRestr hNE).symm z : V) : M) ∈ C) →
      ∀ chi : ℂ → ℝ, ContDiff ℝ 2 chi → HasCompactSupport chi →
      (∀ z, 0 ≤ chi z) → tsupport chi ⊆ D →
      (∫⁻ z, ENNReal.ofReal (chi z *
        ((s.chartDensity (c.subtypeRestr hNE) z)^2 - (q.chartDensity c z)^2))) ≤
        ENNReal.ofReal (B * ∫ z, |Δ chi z|) := by
  obtain ⟨A,hA,hbound⟩ := p.remote_densityRatio_bound hK hC hCK
  refine ⟨Real.log A,Real.log_nonneg hA,?_⟩
  intro V q W s hW hNE c hc D hD hDc hDC chi hchi hcomp hchi0 hsupp
  exact q.chart_gain_cutoff_of_ratio s hNE hc hD hDc hA hchi hcomp hchi0 hsupp
    (fun z hz => hbound V q W s hW _ (hDC z hz))
end AreaDeficit.Surfaces.DiscCover
