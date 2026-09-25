/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DensityRegularity
import BoundedWanderingDomains.Surfaces.CoordinateChainRule
open Set Function Filter Metric
open scoped Manifold Topology
namespace AreaDeficit.Surfaces.DiscCover
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [TopologicalSpace N] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ) 1 N]
theorem density_schwarz_disc (p : DiscCover M) {g : unitDisc → M}
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (v : unitDisc) (hv : g v ∈ c.source) :
    p.density c (g v) * ‖deriv (planeExtension (c ∘ g)) v‖ ≤ discDensity v := by
  let : LocallyPathConnectedSpace unitDisc := ChartedSpace.locallyPathConnectedSpace ℂ unitDisc
  let : SimplyConnectedSpace unitDisc := unitDisc_simplyConnected
  obtain ⟨w,hw⟩ := p.surjective (g v)
  obtain ⟨h,hv0,hfac,hh⟩ := exists_holomorphic_lift p.holomorphic p.covering hg v w hw
  have hwc : p.projection w ∈ c.source := hw ▸ hv
  have hp := ((hc _ hwc).mdifferentiableAt (c.open_source.mem_nhds hwc)).comp w
    (p.holomorphic w)
  have hd := planeExtension_deriv_comp (g := c ∘ p.projection) (h := h)
    (w := v) (hv0.symm ▸ hp) (hh v)
  have hfun : (c ∘ p.projection) ∘ h = c ∘ g := by rw [Function.comp_assoc, hfac]
  rw [hfun, hv0] at hd
  have hs := unitDisc_schwarz hh v
  rw [hv0] at hs
  have hp0 : ‖deriv (planeExtension (c ∘ p.projection)) w‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (p.coordinate_deriv_ne_zero hc hwc)
  rw [← hw, p.density_eq_fibre hc hwc, fibreDensity, hd, norm_mul]
  calc
    _ = discDensity w * ‖deriv (planeExtension (fun z => (h z : ℂ))) v‖ := by field_simp
    _ ≤ discDensity v := hs

theorem density_schwarz (p : DiscCover M) (q : DiscCover N) {f : M → N}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    {c : OpenPartialHomeomorph M ℂ} {d : OpenPartialHomeomorph N ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {x : M} (hxc : x ∈ c.source) (hxd : f x ∈ d.source) :
    q.density d (f x) * ‖deriv (d ∘ f ∘ c.symm) (c x)‖ ≤ p.density c x := by
  obtain ⟨w,rfl⟩ := p.surjective x
  have hs := q.density_schwarz_disc (hf.comp p.holomorphic) hd w hxd
  have he := coordinate_deriv_comp p.holomorphic hf hc hd hxc hxd
  have hp0 : 0 < ‖deriv (planeExtension (c ∘ p.projection)) w‖ :=
    norm_pos_iff.mpr (p.coordinate_deriv_ne_zero hc hxc)
  rw [p.density_eq_fibre hc hxc, fibreDensity]
  apply (le_div_iff₀ hp0).mpr
  have hs' : q.density d (f (p.projection w)) *
      ‖deriv (planeExtension (d ∘ f ∘ p.projection)) w‖ ≤ discDensity w := hs
  rw [he, norm_mul] at hs'
  simpa only [mul_assoc] using hs'
end AreaDeficit.Surfaces.DiscCover
