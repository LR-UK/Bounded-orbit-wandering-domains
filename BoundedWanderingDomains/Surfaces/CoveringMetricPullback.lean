/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.SurfaceSchwarz
import BoundedWanderingDomains.Surfaces.ExtremalDisc

/-! # Exact pullback of the hyperbolic metric through a holomorphic covering -/
open Set Function Filter Metric
open scoped Manifold Topology
namespace AreaDeficit.Surfaces.DiscCover
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [TopologicalSpace N] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ) 1 N]

/-- Schwarz becomes equality for a covering, by lifting the extremal
target disc. No separate surjectivity assumption is needed at a given
source point. -/
theorem density_covering_pullback (p : DiscCover M) (q : DiscCover N)
    {f : M → N} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hcov : IsCoveringMap f)
    {c : OpenPartialHomeomorph M ℂ} {d : OpenPartialHomeomorph N ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {x : M} (hxc : x ∈ c.source) (hxd : f x ∈ d.source) :
    q.density d (f x) * ‖deriv (d ∘ f ∘ c.symm) (c x)‖ = p.density c x := by
  apply le_antisymm (p.density_schwarz q hf hc hd hxc hxd)
  let : SimplyConnectedSpace unitDisc := unitDisc_simplyConnected
  let : LocallyPathConnectedSpace unitDisc := ChartedSpace.locallyPathConnectedSpace ℂ unitDisc
  obtain ⟨g,hg,hg0,he⟩ := q.density_extremal_disc hd hxd
  obtain ⟨h,hh0,hfac,hh⟩ := exists_holomorphic_lift hf hcov hg discZero x hg0.symm
  have hhc : h discZero ∈ c.source := hh0.symm ▸ hxc
  have hhd : f (h discZero) ∈ d.source := by rwa [hh0]
  have hdcomp := coordinate_deriv_comp hh hf hc hd hhc hhd
  have hfun : d ∘ f ∘ h = d ∘ g := congrArg (fun k => d ∘ k) hfac
  rw [hfun,hh0] at hdcomp
  change deriv (planeExtension (d ∘ g)) 0 =
    deriv (d ∘ f ∘ c.symm) (c x) * deriv (planeExtension (c ∘ h)) 0 at hdcomp
  rw [hdcomp,norm_mul] at he
  have hs := p.density_schwarz_disc hh hc discZero hhc
  rw [hh0] at hs
  have hs' : p.density c x * ‖deriv (planeExtension (c ∘ h)) 0‖ ≤ 2 := by
    simpa only [show (discZero : ℂ) = 0 from rfl,discDensity,discDenom,map_zero,
      sub_zero,div_one] using hs
  have hn : 0 < ‖deriv (planeExtension (c ∘ h)) 0‖ := by
    have hnn := norm_nonneg (deriv (planeExtension (c ∘ h)) 0)
    by_contra hn
    have he0 := le_antisymm (le_of_not_gt hn) hnn
    rw [he0,mul_zero,mul_zero] at he
    norm_num at he
  apply (mul_le_mul_iff_left₀ hn).mp
  simpa only [mul_assoc] using hs'.trans_eq he.symm

end AreaDeficit.Surfaces.DiscCover
