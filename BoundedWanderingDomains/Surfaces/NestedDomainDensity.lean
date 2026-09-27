/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DomainCoveringPullback
import BoundedWanderingDomains.Surfaces.DomainAreaSubtype
import BoundedWanderingDomains.Surfaces.DomainLogRatio
import BoundedWanderingDomains.Surfaces.LogDensityRatio

/-! # Comparing an ambient nested domain with its open-subtype model -/

open Set Function Filter TopologicalSpace
open scoped Manifold Topology

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]

/-- Componentwise density is unchanged when nested ambient open sets are
read as an open set of the old-domain subtype. -/
theorem domainDensity_nested_open
    (p : DiscCover M) {U V : Opens M} (hVU : V ≤ U)
    (hUN : Nonempty U) (q : DiscCover U)
    (W : Opens U) (hW : ∀ x : U, x ∈ W ↔ (x : M) ∈ V)
    [ConnectedSpace W] [ConnectedSpace V]
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (x : W) (hxc : ((x : U) : M) ∈ c.source) :
    p.domainDensity V c
        ⟨((x : U) : M), (hW (x : U)).mp x.property⟩ =
      q.domainDensity W (c.subtypeRestr hUN) ⟨(x : U), x.property⟩ := by
  let d := c.subtypeRestr hUN
  let f : U → M := fun y => (y : M)
  have hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f :=
    mdifferentiable_subtype_val U
  have hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source :=
    mdifferentiableOn_subtypeRestr hUN hc
  let xU : U := (x : U)
  have hxW : xU ∈ W := x.property
  have hxV : (xU : M) ∈ V := (hW xU).mp hxW
  have hmap : ∀ z : componentDomain W xU,
      f z ∈ componentDomain V (xU : M) := by
    intro z
    have hCW : componentDomain W xU = W := by
      apply Opens.ext
      exact (isConnected_iff_connectedSpace.mpr inferInstance).isPreconnected
        |>.connectedComponentIn hxW
    have hCV : componentDomain V (xU : M) = V := by
      apply Opens.ext
      exact (isConnected_iff_connectedSpace.mpr inferInstance).isPreconnected
        |>.connectedComponentIn hxV
    rw [hCV]
    apply (hW (z : U)).mp
    simpa only [hCW] using z.property
  have hcov : IsCoveringMap (fun z : componentDomain W xU =>
      (⟨f z, hmap z⟩ : componentDomain V (xU : M))) := by
    let F : componentDomain W xU → componentDomain V (xU : M) :=
      fun z => ⟨f z, hmap z⟩
    let G : componentDomain V (xU : M) → componentDomain W xU := fun y => by
      have hyV : (y : M) ∈ V := componentDomain_le V (xU : M) y.property
      let yU : U := ⟨(y : M), hVU hyV⟩
      have hyW : yU ∈ W := (hW yU).mpr hyV
      have hCW : componentDomain W xU = W := by
        apply Opens.ext
        exact (isConnected_iff_connectedSpace.mpr inferInstance).isPreconnected
          |>.connectedComponentIn hxW
      refine ⟨yU, ?_⟩
      simpa only [hCW] using hyW
    let e : componentDomain W xU ≃ₜ componentDomain V (xU : M) :=
      { toFun := F
        invFun := G
        left_inv := fun z => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => Subtype.ext rfl
        continuous_toFun := by
          apply Continuous.subtype_mk
          exact continuous_subtype_val.comp continuous_subtype_val
        continuous_invFun := by
          apply Continuous.subtype_mk
          apply Continuous.subtype_mk
          exact continuous_subtype_val }
    change IsCoveringMap e
    rw [isCoveringMap_iff_isCoveringMapOn_univ]
    apply e.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    · intro y _
      exact Set.Subsingleton.finite (fun a ha b hb =>
        e.injective (ha.trans hb.symm))
    exact e.isLocalHomeomorph.isLocalHomeomorphOn
  have hpull := q.domainDensity_covering_pullback_components p W V hd hc hf
    hxW (by simpa only [d, OpenPartialHomeomorph.subtypeRestr_source,
      mem_preimage] using hxc) hxV hxc hmap hcov
  have htarget : d xU ∈ d.target := by
    apply d.map_source
    simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage]
      using hxc
  have hevent : (c ∘ f ∘ d.symm) =ᶠ[𝓝 (d xU)] id := by
    filter_upwards [d.open_target.mem_nhds htarget] with z hz
    change c ((d.symm z : U) : M) = z
    have heq : ((d.symm z : U) : M) = c.symm z := by
      simpa only [d, Function.comp_apply] using
        c.subtypeRestr_symm_apply hUN hz
    rw [heq, c.right_inv (c.subtypeRestr_target_subset hUN hz)]
  have hder : deriv (c ∘ f ∘ d.symm) (d xU) = 1 := by
    rw [hevent.deriv_eq]
    simp
  rw [hder, norm_one, mul_one] at hpull
  simpa only [d, f, xU] using hpull

/-- In a chart restricted successively to the old and new domains, the
ambient componentwise log quotient is the ordinary log quotient of the two
supplied subtype disc covers. -/
theorem domainChartLogRatio_eq_nested
    (p : DiscCover M) {U V : Opens M} (hVU : V ≤ U)
    (hUN : Nonempty U) (q : DiscCover U) [ConnectedSpace U]
    (W : Opens U) (hW : ∀ x : U, x ∈ W ↔ (x : M) ∈ V)
    (hWN : Nonempty W) (s : DiscCover W)
    [ConnectedSpace W] [ConnectedSpace V]
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {z : ℂ} (hz : z ∈ ((c.subtypeRestr hUN).subtypeRestr hWN).target) :
    p.domainChartLogRatio U V c z =
      q.chartLogRatio s hWN (c.subtypeRestr hUN) z := by
  let d := c.subtypeRestr hUN
  let e := d.subtypeRestr hWN
  have hzd : z ∈ d.target := d.subtypeRestr_target_subset hWN hz
  have hzc : z ∈ c.target := c.subtypeRestr_target_subset hUN hzd
  have hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source :=
    mdifferentiableOn_subtypeRestr hUN hc
  let xW : W := e.symm z
  let xU : U := (xW : U)
  have hxW : xU ∈ W := xW.property
  have hxV : (xU : M) ∈ V := (hW xU).mp hxW
  have hxe : e xW = z := e.right_inv hz
  have hxd : d xU = z := by
    change d (xW : U) = z
    exact hxe
  have hxc : c (xU : M) = z := by
    change c ((xW : W) : M) = z
    exact hxe
  have hxwe : xW ∈ e.source := by
    change e.symm z ∈ e.source
    exact e.map_target hz
  have hxds : xU ∈ d.source := by
    simpa only [e, OpenPartialHomeomorph.subtypeRestr_source,
      mem_preimage, xU] using hxwe
  have hxsource : (xU : M) ∈ c.source := by
    simpa only [d, OpenPartialHomeomorph.subtypeRestr_source,
      mem_preimage] using hxds
  have hsymm : c.symm z = (xU : M) :=
    (c.symm_apply_eq hxsource hzc).mpr hxc.symm
  have hzU : z ∈ domainChartSet U c := by
    refine ⟨hzc, ?_⟩
    change c.symm z ∈ U
    rw [hsymm]
    exact xU.property
  have hzV : z ∈ domainChartSet V c := by
    refine ⟨hzc, ?_⟩
    change c.symm z ∈ V
    rw [hsymm]
    exact hxV
  have hU := p.domainDensity_eq_connected U q hUN hc xU hxsource
  have hV := p.domainDensity_nested_open hVU hUN q W hW hc xW hxsource
  have hWdens := q.domainDensity_eq_connected W s hWN hd xW (by
    change (xW : U) ∈ d.source
    exact hxds)
  unfold domainChartLogRatio chartLogRatio
  rw [p.domainChartDensity_of_mem U c hzU,
    p.domainChartDensity_of_mem V c hzV]
  have hdsymm : d.symm z = xU := by
    exact (d.symm_apply_eq hxds hzd).mpr hxd.symm
  have hesymm : e.symm z = xW := by
    exact (e.symm_apply_eq hxwe hz).mpr hxe.symm
  simp only [hsymm, hdsymm, hesymm]
  change Real.log (p.domainDensity V c ⟨(xU : M), hxV⟩) -
      Real.log (p.domainDensity U c ⟨(xU : M), xU.property⟩) =
    Real.log (s.density e (e.symm z)) - Real.log (q.density d (d.symm z))
  rw [hV, hU, hWdens, hdsymm, hesymm]

end AreaDeficit.Surfaces.DiscCover

#print axioms AreaDeficit.Surfaces.DiscCover.domainDensity_nested_open
#print axioms AreaDeficit.Surfaces.DiscCover.domainChartLogRatio_eq_nested
