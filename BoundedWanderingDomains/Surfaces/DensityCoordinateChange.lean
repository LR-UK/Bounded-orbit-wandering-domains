/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.SurfaceSchwarz
open Set Function Filter Metric
open scoped Manifold Topology
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]
theorem density_coordinate_change (p : DiscCover M)
    {c d : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {x : M} (hxc : x ∈ c.source) (hxd : x ∈ d.source) :
    p.density d x * ‖deriv (d ∘ c.symm) (c x)‖ = p.density c x := by
  obtain ⟨w,rfl⟩ := p.surjective x
  have he : deriv (planeExtension (d ∘ p.projection)) w =
      deriv (d ∘ c.symm) (c (p.projection w)) *
        deriv (planeExtension (c ∘ p.projection)) w := by
    simpa only [Function.comp_id, Function.id_comp] using
      coordinate_deriv_comp p.holomorphic (mdifferentiable_id (I := 𝓘(ℂ))) hc hd hxc hxd
  have hc0 := p.coordinate_deriv_ne_zero hc hxc
  have hd0 := p.coordinate_deriv_ne_zero hd hxd
  have ht0 : deriv (d ∘ c.symm) (c (p.projection w)) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at he
    exact hd0 he
  rw [p.density_eq_fibre hd hxd, p.density_eq_fibre hc hxc,
    fibreDensity, fibreDensity, he, norm_mul]
  have hcn := norm_ne_zero_iff.mpr hc0
  have htn := norm_ne_zero_iff.mpr ht0
  field_simp

theorem density_sq_coordinate_change (p : DiscCover M)
    {c d : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {x : M} (hxc : x ∈ c.source) (hxd : x ∈ d.source) :
    (p.density d x)^2 * ‖deriv (d ∘ c.symm) (c x)‖^2 = (p.density c x)^2 := by
  rw [← mul_pow, p.density_coordinate_change hc hd hxc hxd]
end AreaDeficit.Surfaces.DiscCover
