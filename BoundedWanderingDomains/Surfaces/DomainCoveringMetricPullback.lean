module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.DomainComponentMap

@[expose] public section

/-! # Componentwise metric pullback from an open-domain covering -/

open Set Function Filter Metric
open scoped Manifold Topology

namespace AreaDeficit.Surfaces.DiscCover

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]
  [TopologicalSpace N] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ) 1 N] [T2Space N] [SecondCountableTopology N]

/-- A holomorphic covering between open domains pulls back their
componentwise hyperbolic densities exactly. -/
theorem domainDensity_covering_pullback
    (p : DiscCover M) (q : DiscCover N)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens N)
    (F : U → V) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hcov : IsCoveringMap F)
    {c : OpenPartialHomeomorph M ℂ} {d : OpenPartialHomeomorph N ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    (x : U) (hxc : (x : M) ∈ c.source) (hxd : (F x : N) ∈ d.source) :
    let C := componentDomain U (x : M)
    let D := componentDomain V (F x : N)
    let G : C → D := domainComponentMap F hF.continuous x
    let cx : C := componentPoint U x
    let dx : D := componentPoint V ⟨F x, (F x).property⟩
    let cr := c.subtypeRestr ⟨cx⟩
    let dr := d.subtypeRestr ⟨dx⟩
    q.domainDensity V d ⟨F x, (F x).property⟩ *
        ‖deriv (dr ∘ G ∘ cr.symm) (cr cx)‖ =
      p.domainDensity U c x := by
  dsimp only
  let C := componentDomain U (x : M)
  let D := componentDomain V (F x : N)
  let G : C → D := domainComponentMap F hF.continuous x
  let cx : C := componentPoint U x
  let dx : D := componentPoint V ⟨F x, (F x).property⟩
  let cr := c.subtypeRestr ⟨cx⟩
  let dr := d.subtypeRestr ⟨dx⟩
  let pc := p.componentCover U x
  let qc := q.componentCover V ⟨F x, (F x).property⟩
  have hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G :=
    domainComponentMap_mdifferentiable F hF x
  have hGcx : G cx = dx := domainComponentMap_componentPoint F hF.continuous x
  have hcxc : cx ∈ cr.source := by
    simpa only [cr, cx, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage,
      componentPoint] using hxc
  have hGd : G cx ∈ dr.source := by
    simpa only [dr, hGcx, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage,
      dx, componentPoint] using hxd
  apply le_antisymm (pc.density_schwarz qc hG
    (mdifferentiableOn_subtypeRestr ⟨cx⟩ hc)
    (mdifferentiableOn_subtypeRestr ⟨dx⟩ hd) hcxc hGd)
  let : SimplyConnectedSpace unitDisc := unitDisc_simplyConnected
  let : LocallyPathConnectedSpace unitDisc :=
    ChartedSpace.locallyPathConnectedSpace ℂ unitDisc
  obtain ⟨g, hg, hg0, he⟩ := qc.density_extremal_disc
    (mdifferentiableOn_subtypeRestr ⟨dx⟩ hd) (by simpa [dr, dx] using hGd)
  let iD : D → V := fun z => ⟨z, componentDomain_le V (F x : N) z.property⟩
  have hiD : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) iD := by
    apply (mdifferentiable_subtypeVal_comp_iff V iD).mp
    have hEq : (Subtype.val ∘ iD : D → N) = (Subtype.val : D → N) := by
      funext z
      rfl
    rw [hEq]
    exact mdifferentiable_subtype_val D
  let gv : unitDisc → V := iD ∘ g
  have hgv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) gv := hiD.comp hg
  have hbase : F x = gv discZero := by
    apply Subtype.ext
    have h := congrArg Subtype.val hg0.symm
    exact h
  obtain ⟨h, hh0, hfac, hh⟩ :=
    exists_holomorphic_lift hF hcov hgv discZero x hbase
  have hhrange : ∀ z, (h z : M) ∈ C := by
    have hunder : Continuous (fun z => (h z : M)) :=
      continuous_subtype_val.comp hh.continuous
    have hr := (isPreconnected_range hunder).subset_connectedComponentIn
      (mem_range_self discZero) (by rintro _ ⟨z, rfl⟩; exact (h z).property)
    intro z
    have hz := hr (mem_range_self z)
    rw [show (h discZero : M) = x from congrArg Subtype.val hh0] at hz
    exact hz
  let H : unitDisc → C := fun z => ⟨h z, hhrange z⟩
  have hH : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H := by
    apply (mdifferentiable_subtypeVal_comp_iff C H).mp
    have hEq : (Subtype.val ∘ H : unitDisc → M) =
        (Subtype.val : U → M) ∘ h := by
      funext z
      rfl
    rw [hEq]
    exact (mdifferentiable_subtype_val U).comp hh
  have hH0 : H discZero = cx := by
    apply Subtype.ext
    change (h discZero : M) = x
    exact congrArg Subtype.val hh0
  have hGH : G ∘ H = g := by
    funext z
    apply Subtype.ext
    have hz := congrFun hfac z
    change (F (h z) : N) = (g z : N)
    exact congrArg Subtype.val hz
  have hhc : H discZero ∈ cr.source := hH0.symm ▸ hcxc
  have hhd : G (H discZero) ∈ dr.source := by rwa [hH0]
  have hdcomp := coordinate_deriv_comp hH hG
    (mdifferentiableOn_subtypeRestr ⟨cx⟩ hc)
    (mdifferentiableOn_subtypeRestr ⟨dx⟩ hd) hhc hhd
  have hfun : dr ∘ G ∘ H = dr ∘ g := congrArg (fun k => dr ∘ k) hGH
  rw [hfun, hH0] at hdcomp
  change deriv (planeExtension (dr ∘ g)) 0 =
    deriv (dr ∘ G ∘ cr.symm) (cr cx) *
      deriv (planeExtension (cr ∘ H)) 0 at hdcomp
  rw [hdcomp, norm_mul] at he
  have hs := pc.density_schwarz_disc hH
    (mdifferentiableOn_subtypeRestr ⟨cx⟩ hc) discZero hhc
  rw [hH0] at hs
  have hs' : pc.density cr cx * ‖deriv (planeExtension (cr ∘ H)) 0‖ ≤ 2 := by
    simpa only [show (discZero : ℂ) = 0 from rfl, discDensity, discDenom,
      map_zero, sub_zero, div_one] using hs
  have hn : 0 < ‖deriv (planeExtension (cr ∘ H)) 0‖ := by
    have hnn := norm_nonneg (deriv (planeExtension (cr ∘ H)) 0)
    by_contra hn
    have he0 := le_antisymm (le_of_not_gt hn) hnn
    rw [he0, mul_zero, mul_zero] at he
    norm_num at he
  apply (mul_le_mul_iff_left₀ hn).mp
  simpa only [mul_assoc] using hs'.trans_eq he.symm

end AreaDeficit.Surfaces.DiscCover
