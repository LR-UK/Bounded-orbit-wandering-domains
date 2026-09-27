/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.ConformalLaplacian
import BoundedWanderingDomains.Surfaces.ChartCriticalValues

/-! # Conformal change of the coordinate Laplacian -/

open Set Function Filter InnerProductSpace Laplacian
open scoped Manifold Topology ContDiff

namespace AreaDeficit.Surfaces

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]

/-- A scalar function's Euclidean coordinate Laplacians transform by the
square norm of the holomorphic transition derivative. -/
theorem laplacian_coordinate_change
    {c d : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {u : M → ℝ} {x : M} (hxc : x ∈ c.source) (hxd : x ∈ d.source)
    (hu : ContDiffAt ℝ 2 (u ∘ d.symm) (d x)) :
    Δ (u ∘ c.symm) (c x) =
      ‖deriv (d ∘ c.symm) (c x)‖ ^ 2 * Δ (u ∘ d.symm) (d x) := by
  let g : ℂ → ℂ := d ∘ c.symm
  have hg : AnalyticAt ℂ g (c x) := by
    simpa only [g, Function.comp_id, Function.id_comp] using
      SurfaceDynamics.analyticAt_writtenInCharts hc hd
        (mdifferentiable_id (I := 𝓘(ℂ))) hxc hxd
  have he : u ∘ c.symm =ᶠ[𝓝 (c x)] (u ∘ d.symm) ∘ g := by
    have hct : ∀ᶠ z in 𝓝 (c x), z ∈ c.target :=
      c.open_target.mem_nhds (c.map_source hxc)
    have hcont : ContinuousAt c.symm (c x) :=
      c.continuousAt_symm (c.map_source hxc)
    have hds : ∀ᶠ z in 𝓝 (c x), c.symm z ∈ d.source := by
      apply hcont
      simpa only [c.left_inv hxc] using d.open_source.mem_nhds hxd
    filter_upwards [hct, hds] with z hzc hzd
    simp only [g, comp_apply, d.left_inv hzd]
  rw [(laplacian_congr_nhds he).eq_of_nhds]
  have hu' : ContDiffAt ℝ 2 (u ∘ d.symm) (g (c x)) := by
    simpa only [g, comp_apply, c.left_inv hxc] using hu
  have hchain := AreaDeficit.laplacian_comp_holomorphic hu' hg
  simpa only [g, comp_apply, c.left_inv hxc] using hchain

end AreaDeficit.Surfaces
