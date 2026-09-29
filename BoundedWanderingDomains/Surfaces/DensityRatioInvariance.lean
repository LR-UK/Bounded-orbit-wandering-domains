module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.LogDensityRatio

@[expose] public section
open Set Function Filter Metric MeasureTheory
open scoped Manifold Topology ENNReal
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]
theorem density_ratio_coordinate_independent (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (hU : Nonempty U) {c d : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {x : U} (hxc : (x : M) ∈ c.source) (hxd : (x : M) ∈ d.source) :
    q.density (c.subtypeRestr hU) x / p.density c x =
      q.density (d.subtypeRestr hU) x / p.density d x := by
  let cU := c.subtypeRestr hU
  let dU := d.subtypeRestr hU
  have hxcU : x ∈ cU.source := by
    simpa only [cU,OpenPartialHomeomorph.subtypeRestr_source,mem_preimage] using hxc
  have hxdU : x ∈ dU.source := by
    simpa only [dU,OpenPartialHomeomorph.subtypeRestr_source,mem_preimage] using hxd
  have he : (dU ∘ cU.symm) =ᶠ[𝓝 (c x)] (d ∘ c.symm) := by
    have hcx : c x ∈ cU.target := cU.map_source hxcU
    filter_upwards [cU.open_target.mem_nhds hcx] with z hz
    change d ((cU.symm z : U) : M) = d (c.symm z)
    rw [show (cU.symm z : M) = c.symm z from c.subtypeRestr_symm_apply hU hz]
  have hp := p.density_coordinate_change hc hd hxc hxd
  have hq := q.density_coordinate_change (mdifferentiableOn_subtypeRestr hU hc)
    (mdifferentiableOn_subtypeRestr hU hd) hxcU hxdU
  change q.density dU x * ‖deriv (dU ∘ cU.symm) (c x)‖ = q.density cU x at hq
  rw [he.deriv_eq] at hq
  have hD : ‖deriv (d ∘ c.symm) (c x)‖ ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hp
    exact (ne_of_gt (p.density_pos hc hxc)) hp.symm
  change q.density cU x / p.density c x = q.density dU x / p.density d x
  rw [← hp,← hq]
  exact mul_div_mul_right _ _ hD
noncomputable def densityRatio (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (x : U) : ℝ :=
  q.density ((chartAt ℂ (x : M)).subtypeRestr ⟨x⟩) x /
    p.density (chartAt ℂ (x : M)) x

theorem densityRatio_eq (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (hU : Nonempty U) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {x : U} (hx : (x : M) ∈ c.source) :
    p.densityRatio q x = q.density (c.subtypeRestr hU) x / p.density c x := by
  have hc₀ : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ (x : M))
      (chartAt ℂ (x : M)).source := fun z hz =>
    (mdifferentiableAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas _) hz).mdifferentiableWithinAt
  exact p.density_ratio_coordinate_independent q hU hc₀ hc (mem_chart_source ℂ (x : M)) hx

theorem one_le_densityRatio (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (x : U) : 1 ≤ p.densityRatio q x := by
  let c := chartAt ℂ (x : M)
  have hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source := fun z hz =>
    (mdifferentiableAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas _) hz).mdifferentiableWithinAt
  have hx : (x : M) ∈ c.source := mem_chart_source ℂ (x : M)
  rw [p.densityRatio_eq q ⟨x⟩ hc hx]
  exact (le_div_iff₀ (p.density_pos hc hx)).mpr (by
    simpa only [one_mul] using p.density_subdomain_le q ⟨x⟩ hc hx)
end AreaDeficit.Surfaces.DiscCover
