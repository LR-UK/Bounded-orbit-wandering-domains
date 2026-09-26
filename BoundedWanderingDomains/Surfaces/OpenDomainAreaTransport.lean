/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DomainCoveringMetricPullback
import BoundedWanderingDomains.Surfaces.DomainMapAreaTransport

/-! # Exact area transport through a covering of open surface domains -/

open Set Function Filter MeasureTheory
open scoped Manifold Topology ENNReal

namespace AreaDeficit.Surfaces.DiscCover

set_option maxHeartbeats 800000

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ) 1 N] [MeasurableSpace N] [BorelSpace N]
  [SecondCountableTopology N] [T2Space N]

/-- A holomorphic covering between open domains preserves intrinsic area on
every measurable chart patch on which it is injective.  The ambient map need
only agree with the covering on the source domain; no global holomorphic
extension is required. -/
theorem chart_domainArea_eq_image_of_openDomain_covering
    (p : DiscCover M) (q : DiscCover N)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens N)
    (F : U → V) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hcov : IsCoveringMap F)
    {f : M → N} (hf : (fun x : U => f x) = (fun x => (F x : N)))
    {c : OpenPartialHomeomorph M ℂ} {d : OpenPartialHomeomorph N ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {W : Set M} (hW : MeasurableSet W)
    (hWU : W ⊆ U) (hWc : W ⊆ c.source)
    (hfWd : f '' W ⊆ d.source) (hfW : MeasurableSet (f '' W))
    (hinj : InjOn f W) :
    p.domainArea U W = q.domainArea V (f '' W) := by
  apply p.chart_domainArea_eq_image_of_pullback_local q U V hc hd hW hWc hfWd hfW hinj
  · rintro _ ⟨x, hx, rfl⟩
    have hfxd : f x ∈ d.source := hfWd ⟨x, hx, rfl⟩
    have hfat : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x := by
      refine (mdifferentiableAt_subtype_iff
        (U := U) (f := f) (x := (⟨x, hWU hx⟩ : U))).mp ?_
      rw [hf]
      exact ((mdifferentiable_subtype_val V).comp hF) ⟨x, hWU hx⟩
    have hci := (mdifferentiableOn_symm hc _ (c.map_source (hWc hx))).mdifferentiableAt
      (c.open_target.mem_nhds (c.map_source (hWc hx)))
    have hfat' : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (c.symm (c x)) := by
      rwa [c.left_inv (hWc hx)]
    have hfi := hfat'.comp (c x) hci
    have hdi := (hd _ hfxd).mdifferentiableAt (d.open_source.mem_nhds hfxd)
    have hdi' : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) d ((f ∘ c.symm) (c x)) := by
      simpa only [comp_apply, c.left_inv (hWc hx)] using hdi
    simpa only [c.left_inv (hWc hx)] using
      (hdi'.comp (c x) hfi).differentiableAt.hasDerivAt
  · rintro _ ⟨x, hx, rfl⟩
    let xU : U := ⟨x, hWU hx⟩
    have hfx : (F xU : N) = f x := by
      have := congrFun hf xU
      exact this.symm
    have hfxd : (F xU : N) ∈ d.source := hfx.symm ▸ hfWd ⟨x, hx, rfl⟩
    have hpull := p.domainDensity_covering_pullback q U V F hF hcov hc hd
      xU (hWc hx) hfxd
    let C := componentDomain U x
    let D := componentDomain V (F xU : N)
    let G : C → D := domainComponentMap F hF.continuous xU
    let cx : C := componentPoint U xU
    let dx : D := componentPoint V ⟨F xU, (F xU).property⟩
    let cr := c.subtypeRestr ⟨cx⟩
    let dr := d.subtypeRestr ⟨dx⟩
    have hcxc : cx ∈ cr.source := by
      simpa only [cr, cx, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage,
        componentPoint] using hWc hx
    have hevent : (dr ∘ G ∘ cr.symm) =ᶠ[𝓝 (cr cx)] (d ∘ f ∘ c.symm) := by
      filter_upwards [cr.open_target.mem_nhds (cr.map_source hcxc)] with z hz
      have he := c.subtypeRestr_symm_apply ⟨cx⟩ hz
      have hu : ((cr.symm z : C) : M) ∈ U :=
        componentDomain_le U x (cr.symm z).property
      have hres := congrFun hf (⟨((cr.symm z : C) : M), hu⟩ : U)
      change d (F ⟨((cr.symm z : C) : M), hu⟩) = d (f (c.symm z))
      exact congrArg d (hres.symm.trans (congrArg f he))
    have hder : deriv (dr ∘ G ∘ cr.symm) (cr cx) =
        deriv (d ∘ f ∘ c.symm) (c x) := by
      rw [hevent.deriv_eq]
      rfl
    have hzc : c x ∈ domainChartSet U c :=
      ⟨c.map_source (hWc hx), by simpa [c.left_inv (hWc hx)] using hWU hx⟩
    have hzd : d (f x) ∈ domainChartSet V d :=
      ⟨d.map_source (hfWd ⟨x, hx, rfl⟩), by
        have : f x ∈ V := hfx ▸ (F xU).property
        simpa [d.left_inv (hfWd ⟨x, hx, rfl⟩)] using this⟩
    simp only [comp_apply, c.left_inv (hWc hx)]
    rw [p.domainChartDensity_of_mem U c hzc,
      q.domainChartDensity_of_mem V d hzd]
    have hs : (⟨c.symm (c x), hzc.2⟩ : U) = xU :=
      Subtype.ext (c.left_inv (hWc hx))
    have ht : (⟨d.symm (d (f x)), hzd.2⟩ : V) =
        ⟨F xU, (F xU).property⟩ := by
      apply Subtype.ext
      exact (d.left_inv (hfWd ⟨x, hx, rfl⟩)).trans hfx.symm
    rw [hs, ht, ← hder, mul_comm]
    exact hpull

end AreaDeficit.Surfaces.DiscCover

#print axioms AreaDeficit.Surfaces.DiscCover.chart_domainArea_eq_image_of_openDomain_covering
