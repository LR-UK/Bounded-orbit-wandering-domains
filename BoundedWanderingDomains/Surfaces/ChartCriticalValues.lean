module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.ChartMapAreaTransport
public import BoundedWanderingDomains.Surfaces.OpenMapping
public import BoundedWanderingDomains.LocalCovering

@[expose] public section

/-! # Finiteness of branch values on one compact chart patch -/

open Set Function Filter Topology
open scoped Manifold Topology

namespace SurfaceDynamics

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]
  [TopologicalSpace N] [ChartedSpace ℂ N]

/-- A holomorphic surface map written in a fixed source/target chart pair is
analytic at every point where both charts apply. -/
theorem analyticAt_writtenInCharts
    {c : OpenPartialHomeomorph M ℂ} {d : OpenPartialHomeomorph N ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {f : M → N} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    {x : M} (hxc : x ∈ c.source) (hfd : f x ∈ d.source) :
    AnalyticAt ℂ (d ∘ f ∘ c.symm) (c x) := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hct : c.target ∈ 𝓝 (c x) := c.open_target.mem_nhds (c.map_source hxc)
  have hcont : ContinuousAt (f ∘ c.symm) (c x) := by
    have hf_at : ContinuousAt f (c.symm (c x)) := by
      simpa only [c.left_inv hxc] using (hf x).continuousAt
    exact hf_at.comp (c.continuousAt_symm (c.map_source hxc))
  have hfd' : (f ∘ c.symm) (c x) ∈ d.source := by
    change f (c.symm (c x)) ∈ d.source
    rw [c.left_inv hxc]
    exact hfd
  have hdt : ∀ᶠ z in 𝓝 (c x), f (c.symm z) ∈ d.source :=
    hcont (d.open_source.mem_nhds hfd')
  filter_upwards [hct, hdt] with z hzc hzd
  have hsource : c.symm z ∈ c.source := c.map_target hzc
  have hh := AreaDeficit.Surfaces.DiscCover.hasDerivAt_writtenInCharts
    hc hd hf hsource hzd
  rw [c.right_inv hzc] at hh
  exact hh.differentiableAt

omit [IsManifold 𝓘(ℂ) 1 M] in
/-- Openness rules out a constant germ in every fixed chart reading. -/
theorem not_eventuallyConst_writtenInCharts
    {c : OpenPartialHomeomorph M ℂ} {d : OpenPartialHomeomorph N ℂ}
    {f : M → N} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hopen : IsOpenMap f) {x : M} (hxc : x ∈ c.source)
    (hfd : f x ∈ d.source) :
    ¬ EventuallyConst (d ∘ f ∘ c.symm) (𝓝 (c x)) := by
  intro hconst
  apply not_eventuallyEq_const_of_isOpenMap hopen x
  have hccont : Tendsto c (𝓝 x) (𝓝 (c x)) := c.continuousAt hxc
  obtain ⟨a, ha⟩ := hconst.eventuallyEq_const
  have hg := ha.comp_tendsto hccont
  have hax : (d ∘ f ∘ c.symm) (c x) = a := ha.self_of_nhds
  have hcs : ∀ᶠ y in 𝓝 x, y ∈ c.source := c.open_source.mem_nhds hxc
  have hds : ∀ᶠ y in 𝓝 x, f y ∈ d.source :=
    (hf x).continuousAt (d.open_source.mem_nhds hfd)
  filter_upwards [hg, hcs, hds] with y hgy hyc hyd
  have hcoord : d (f y) = d (f x) := by
    have := hgy.trans hax.symm
    simpa only [comp_apply, c.left_inv hyc, c.left_inv hxc] using this
  exact d.injOn hyd hfd hcoord

/-- In a compact set contained in one source chart and mapped into one target
chart, only finitely many points have vanishing coordinate derivative. -/
theorem finite_chart_critical_points
    {c : OpenPartialHomeomorph M ℂ} {d : OpenPartialHomeomorph N ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {f : M → N} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hopen : IsOpenMap f) {K : Set M} (hK : IsCompact K)
    (hKc : K ⊆ c.source) (hfKd : f '' K ⊆ d.source) :
    (K ∩ {x | deriv (d ∘ f ∘ c.symm) (c x) = 0}).Finite := by
  let g : ℂ → ℂ := d ∘ f ∘ c.symm
  have hKimage : IsCompact (c '' K) :=
    hK.image_of_continuousOn (c.continuousOn.mono hKc)
  have hgan : AnalyticOnNhd ℂ g (c '' K) := by
    rintro _ ⟨x, hx, rfl⟩
    exact analyticAt_writtenInCharts hc hd hf (hKc hx) (hfKd ⟨x, hx, rfl⟩)
  have hgnc : ∀ z ∈ c '' K, ¬ EventuallyConst g (𝓝 z) := by
    rintro _ ⟨x, hx, rfl⟩
    exact not_eventuallyConst_writtenInCharts hf hopen (hKc hx) (hfKd ⟨x, hx, rfl⟩)
  have hplane := AreaDeficit.finite_local_critical_points hKimage hgan hgnc
  apply Set.Finite.of_finite_image (f := c)
  · apply hplane.subset
    rintro _ ⟨x, ⟨hxK, hxcrit⟩, rfl⟩
    exact ⟨⟨x, hxK, rfl⟩, hxcrit⟩
  · exact c.injOn.mono (inter_subset_left.trans hKc)

/-- The corresponding set of branch values is finite. -/
theorem finite_chart_critical_values
    {c : OpenPartialHomeomorph M ℂ} {d : OpenPartialHomeomorph N ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {f : M → N} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hopen : IsOpenMap f) {K : Set M} (hK : IsCompact K)
    (hKc : K ⊆ c.source) (hfKd : f '' K ⊆ d.source) :
    (f '' (K ∩ {x | deriv (d ∘ f ∘ c.symm) (c x) = 0})).Finite :=
  (finite_chart_critical_points hc hd hf hopen hK hKc hfKd).image f

end SurfaceDynamics
