/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.HyperbolicArea
open Set Function Filter Metric MeasureTheory
open scoped Manifold Topology ENNReal
namespace AreaDeficit.Surfaces
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]
omit [IsManifold 𝓘(ℂ) 1 M] in
theorem mdifferentiableOn_subtypeRestr {U : TopologicalSpace.Opens M} (hU : Nonempty U)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (c.subtypeRestr hU) (c.subtypeRestr hU).source := by
  intro x hx
  have hxc : (x : M) ∈ c.source := by simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hx
  have hd := ((hc _ hxc).mdifferentiableAt (c.open_source.mem_nhds hxc)).comp x
    (mdifferentiable_subtype_val U x)
  exact hd.mdifferentiableWithinAt
namespace DiscCover
theorem density_subdomain_le (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (hU : Nonempty U) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {x : U} (hx : (x : M) ∈ c.source) :
    p.density c x ≤ q.density (c.subtypeRestr hU) x := by
  let d := c.subtypeRestr hU
  have hd := mdifferentiableOn_subtypeRestr hU hc
  have hxd : x ∈ d.source := by simpa only [d,OpenPartialHomeomorph.subtypeRestr_source,mem_preimage] using hx
  have hs := q.density_schwarz p (mdifferentiable_subtype_val U) hd hc hxd hx
  have he : (c ∘ Subtype.val ∘ d.symm) =ᶠ[𝓝 (d x)] id := by
    filter_upwards [d.open_target.mem_nhds (d.map_source hxd)] with z hz
    exact d.right_inv hz
  have hder : deriv (c ∘ Subtype.val ∘ d.symm) (d x) = 1 := by
    rw [he.deriv_eq]
    simp
  change p.density c x * ‖deriv (c ∘ Subtype.val ∘ d.symm) (d x)‖ ≤
    q.density d x at hs
  simpa only [hder,norm_one,mul_one] using hs

theorem chartDensity_subdomain_le (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (hU : Nonempty U) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {z : ℂ} (hz : z ∈ (c.subtypeRestr hU).target) :
    p.chartDensity c z ≤ q.chartDensity (c.subtypeRestr hU) z := by
  have hx := (c.subtypeRestr hU).map_target hz
  have hxc : ((c.subtypeRestr hU).symm z : M) ∈ c.source := by
    simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hx
  have hs := p.density_subdomain_le q hU hc hxc
  have he := c.subtypeRestr_symm_apply hU hz
  change ((c.subtypeRestr hU).symm z : M) = c.symm z at he
  change p.density c (c.symm z) ≤ q.density (c.subtypeRestr hU) ((c.subtypeRestr hU).symm z)
  rw [← he]
  exact hs
end DiscCover
end AreaDeficit.Surfaces
