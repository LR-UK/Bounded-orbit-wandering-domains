/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.Surfaces.LogDensityRatio
import BoundedWanderingDomains.DensityDeficit

/-! # A proved local cutoff estimate for the surface area gain

This is the analytic chart step: the logarithmic-ratio bound is an explicit
hypothesis here. The full uniform remote-removal theorem must still derive
that bound from geometric separation and assemble the chart estimates.
-/
open Set Function Filter Metric MeasureTheory InnerProductSpace Laplacian
open scoped Manifold Topology ENNReal ContDiff
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

theorem chart_gain_cutoff (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (hU : Nonempty U) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {V : Set ℂ} (hV : IsOpen V) (hVc : V ⊆ (c.subtypeRestr hU).target)
    {chi : ℂ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hchi : ContDiff ℝ 2 chi) (hcomp : HasCompactSupport chi)
    (hchi0 : ∀ z, 0 ≤ chi z) (hsupp : tsupport chi ⊆ V)
    (hbound : ∀ z ∈ V, p.chartLogRatio q hU c z ≤ B) :
    (∫⁻ z, ENNReal.ofReal (chi z *
      ((q.chartDensity (c.subtypeRestr hU) z)^2 - (p.chartDensity c z)^2))) ≤
      ENNReal.ofReal (B * ∫ z, |Δ chi z|) := by
  have hd := mdifferentiableOn_subtypeRestr hU hc
  have hmain := density_deficit_cutoff (∅ : Finset ℂ) hV hB hchi hcomp hchi0 hsupp
    (a := q.chartDensity (c.subtypeRestr hU)) (b := p.chartDensity c)
    (fun z hz _ => ⟨q.chartDensity_pos hd (hVc hz),q.chartDensity_contDiffAt hd (hVc hz)⟩)
    (fun z hz _ => ⟨p.chartDensity_pos hc (c.subtypeRestr_target_subset hU (hVc hz)),
      p.chartDensity_contDiffAt hc (c.subtypeRestr_target_subset hU (hVc hz))⟩)
    (fun z hz _ => q.chartDensity_curvature hd (hVc hz))
    (fun z hz _ => p.chartDensity_curvature hc (c.subtypeRestr_target_subset hU (hVc hz)))
    (fun z hz _ => max_le (hbound z hz) hB)
  convert hmain using 1
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ tsupport chi
  · have hnonneg : 0 ≤ (q.chartDensity (c.subtypeRestr hU) z)^2 -
        (p.chartDensity c z)^2 := by
      rw [← p.chartLogRatio_laplacian q hU hc (hVc (hsupp hz))]
      exact p.chartLogRatio_laplacian_nonneg q hU hc (hVc (hsupp hz))
    simp only [Finset.notMem_empty,ite_false,max_eq_left hnonneg]
  · simp [image_eq_zero_of_notMem_tsupport hz]

end AreaDeficit.Surfaces.DiscCover
