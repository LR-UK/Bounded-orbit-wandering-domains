/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DomainMapAreaTransport
import BoundedWanderingDomains.Surfaces.SubtypeHolomorphic

/-! # Pullback of componentwise hyperbolic subdomain metrics -/

open Set Function Filter
open scoped Manifold Topology

namespace AreaDeficit.Surfaces.DiscCover

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]
  [TopologicalSpace N] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ) 1 N] [T2Space N] [SecondCountableTopology N]

/-- If the restriction of a holomorphic map between the relevant connected
components is a covering, their componentwise hyperbolic densities satisfy
the exact pullback identity. -/
theorem domainDensity_covering_pullback_components
    (p : DiscCover M) (q : DiscCover N)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens N)
    {c : OpenPartialHomeomorph M ℂ} {d : OpenPartialHomeomorph N ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {f : M → N} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    {x : M} (hxU : x ∈ U) (hxc : x ∈ c.source)
    (hfxV : f x ∈ V) (hfxd : f x ∈ d.source)
    (hmap : ∀ z : componentDomain U x,
      f z ∈ componentDomain V (f x))
    (hcov : IsCoveringMap (fun z : componentDomain U x =>
      (⟨f z, hmap z⟩ : componentDomain V (f x)))) :
    q.domainDensity V d ⟨f x, hfxV⟩ *
        ‖deriv (d ∘ f ∘ c.symm) (c x)‖ =
      p.domainDensity U c ⟨x, hxU⟩ := by
  let xU : U := ⟨x, hxU⟩
  let yV : V := ⟨f x, hfxV⟩
  let CU := componentDomain U x
  let CV := componentDomain V (f x)
  let F : CU → CV := fun z => ⟨f z, hmap z⟩
  have hFval : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Subtype.val ∘ F) := by
    have hsub : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Subtype.val : CU → M) :=
      mdifferentiable_subtype_val CU
    have hcomp := hf.comp hsub
    have heq : (Subtype.val ∘ F : CU → N) = f ∘ (Subtype.val : CU → M) := by
      funext z
      rfl
    rw [heq]
    exact hcomp
  have hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F :=
    (mdifferentiable_subtypeVal_comp_iff CV F).mp hFval
  let pc : DiscCover CU := p.componentCover U xU
  let qc : DiscCover CV := q.componentCover V yV
  let cx : CU := componentPoint U xU
  have hFcx : F cx = componentPoint V yV := Subtype.ext rfl
  have hcx : cx ∈ (c.subtypeRestr ⟨cx⟩).source := by
    simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage, cx,
      componentPoint] using hxc
  have hdx : F cx ∈ (d.subtypeRestr ⟨componentPoint V yV⟩).source := by
    simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage, hFcx,
      componentPoint] using hfxd
  have hpull := pc.density_covering_pullback qc hF hcov
    (mdifferentiableOn_subtypeRestr ⟨cx⟩ hc)
    (mdifferentiableOn_subtypeRestr ⟨componentPoint V yV⟩ hd) hcx hdx
  let cr := c.subtypeRestr ⟨cx⟩
  let dr := d.subtypeRestr ⟨componentPoint V yV⟩
  have hevent : (dr ∘ F ∘ cr.symm) =ᶠ[𝓝 (cr cx)] (d ∘ f ∘ c.symm) := by
    filter_upwards [cr.open_target.mem_nhds (cr.map_source hcx)] with z hz
    change d (f (((cr.symm z : CU) : M))) = d (f (c.symm z))
    rw [show ((cr.symm z : CU) : M) = c.symm z from
      c.subtypeRestr_symm_apply ⟨cx⟩ hz]
  have hder : deriv (dr ∘ F ∘ cr.symm) (cr cx) =
      deriv (d ∘ f ∘ c.symm) (c x) := by
    rw [hevent.deriv_eq]
    rfl
  change qc.density dr (componentPoint V yV) *
      ‖deriv (d ∘ f ∘ c.symm) (c x)‖ = pc.density cr cx
  rw [← hFcx, ← hder]
  exact hpull

end AreaDeficit.Surfaces.DiscCover
