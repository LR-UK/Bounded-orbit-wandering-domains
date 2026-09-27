/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.NestedDomainDensity
import BoundedWanderingDomains.Surfaces.OldPunctureBoundaryMass
import BoundedWanderingDomains.Surfaces.PunctureBoundaryMass
import BoundedWanderingDomains.CutoffError

/-! # Boundary-mass estimates transported to nested ambient domains -/

open Set Function Filter Metric MeasureTheory InnerProductSpace Laplacian
open scoped Manifold Topology

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]

/-- A point in a twice-restricted chart target lies in the ambient chart
set of the corresponding nested domain. -/
theorem mem_domainChartSet_of_mem_nested_target
    {U V : TopologicalSpace.Opens M} (hUN : Nonempty U)
    (W : TopologicalSpace.Opens U)
    (hW : ∀ x : U, x ∈ W ↔ (x : M) ∈ V) (hWN : Nonempty W)
    (c : OpenPartialHomeomorph M ℂ) {z : ℂ}
    (hz : z ∈ ((c.subtypeRestr hUN).subtypeRestr hWN).target) :
    z ∈ domainChartSet V c := by
  let d := c.subtypeRestr hUN
  let e := d.subtypeRestr hWN
  have hzd : z ∈ d.target := d.subtypeRestr_target_subset hWN hz
  have hzc : z ∈ c.target := c.subtypeRestr_target_subset hUN hzd
  have he := d.subtypeRestr_symm_apply hWN hz
  have hd := c.subtypeRestr_symm_apply hUN hzd
  have he' : ((e.symm z : W) : U) = d.symm z := by
    simpa only [e, Function.comp_apply] using he
  have hd' : ((d.symm z : U) : M) = c.symm z := by
    simpa only [d, Function.comp_apply] using hd
  refine ⟨hzc, ?_⟩
  change c.symm z ∈ V
  rw [← hd']
  apply (hW (d.symm z)).mp
  rw [← he']
  exact (e.symm z).property

/-- On sufficiently small logarithmic annuli, the ambient componentwise
boundary pairing is exactly the pairing of supplied covers of the two nested
open subtypes. -/
theorem eventually_domainChart_boundary_eq_nested
    (p : DiscCover M) {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    (hUN : Nonempty U) (q : DiscCover U) [ConnectedSpace U]
    (W : TopologicalSpace.Opens U)
    (hW : ∀ x : U, x ∈ W ↔ (x : M) ∈ V)
    (hWN : Nonempty W) (s : DiscCover W)
    [ConnectedSpace W] [ConnectedSpace V]
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : ball a R \ {a} ⊆
      ((c.subtypeRestr hUN).subtypeRestr hWN).target) :
    ∀ᶠ t : ℝ in atTop,
      (∫ z : ℂ, p.domainChartLogRatio U V c z *
        Δ (AreaDeficit.logCutoff a (-2 * t) (-t)) z) =
      ∫ z : ℂ, q.chartLogRatio s hWN (c.subtypeRestr hUN) z *
        Δ (AreaDeficit.logCutoff a (-2 * t) (-t)) z := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_gt_atTop (-Real.log R)] with t ht htR
  apply integral_congr_ae
  filter_upwards with z
  by_cases hlap : Δ (AreaDeficit.logCutoff a (-2 * t) (-t)) z = 0
  · rw [hlap, mul_zero, mul_zero]
  · obtain ⟨hza, -, hzlog⟩ :=
      AreaDeficit.logCutoff_laplacian_ne_zero (by linarith) hlap
    have hn : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hza)
    have hzR : ‖z - a‖ < R := by
      apply (Real.log_lt_log_iff hn hR).mp
      exact hzlog.trans (by linarith)
    have hzt : z ∈ ((c.subtypeRestr hUN).subtypeRestr hWN).target :=
      hball ⟨by simpa only [mem_ball, dist_eq_norm] using hzR,
        by simpa only [mem_singleton_iff] using hza⟩
    rw [p.domainChartLogRatio_eq_nested hVU hUN q W hW hWN s hc hzt]

/-- Old-end vanishing for supplied nested covers, read back as an ambient
componentwise boundary pairing. -/
theorem tendsto_domainChart_old_boundary_mass_zero
    (p : DiscCover M) {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    (hUN : Nonempty U) (q : DiscCover U) [ConnectedSpace U]
    {K : Set U} (hK : IsCompact K)
    (W : TopologicalSpace.Opens U)
    (hWK : ∀ y : U, y ∈ W ↔ y ∉ K)
    (hW : ∀ x : U, x ∈ W ↔ (x : M) ∈ V)
    (hWN : Nonempty W) (s : DiscCover W)
    [ConnectedSpace W] [ConnectedSpace V]
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : ball a R \ {a} ⊆
      ((c.subtypeRestr hUN).subtypeRestr hWN).target)
    (x : ℂ → W)
    (hx : Tendsto (fun z => (x z : U)) (𝓝[≠] a) (cocompact U))
    (hcoord : ∀ᶠ z in 𝓝[≠] a,
      z ∈ ((c.subtypeRestr hUN).subtypeRestr hWN).target ∧
        x z = ((c.subtypeRestr hUN).subtypeRestr hWN).symm z) :
    Tendsto (fun t : ℝ => ∫ z : ℂ,
      p.domainChartLogRatio U V c z *
        Δ (AreaDeficit.logCutoff a (-2 * t) (-t)) z)
      atTop (𝓝 0) := by
  have hnested := q.tendsto_old_puncture_boundary_mass_zero hK hWK s
    (mdifferentiableOn_subtypeRestr hUN hc) x hx hcoord
  have heq := p.eventually_domainChart_boundary_eq_nested hVU hUN q W hW
    hWN s hc hR hball
  apply hnested.congr'
  filter_upwards [heq] with t ht
  exact ht.symm

/-- The new-end uniform bound for supplied nested covers, read back as an
ambient componentwise boundary pairing. -/
theorem eventually_bounded_domainChart_new_boundary_mass
    (p : DiscCover M) {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    (hUN : Nonempty U) (q : DiscCover U) [ConnectedSpace U]
    (W : TopologicalSpace.Opens U)
    (hW : ∀ x : U, x ∈ W ↔ (x : M) ∈ V)
    (hWN : Nonempty W) (s : DiscCover W)
    [ConnectedSpace W] [ConnectedSpace V]
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {a : ℂ} (ha : a ∈ (c.subtypeRestr hUN).target)
    {R : ℝ} (hR : 0 < R)
    (hball : ball a R \ {a} ⊆
      ((c.subtypeRestr hUN).subtypeRestr hWN).target) :
    ∀ᶠ t : ℝ in atTop,
      |∫ z : ℂ, p.domainChartLogRatio U V c z *
        Δ (AreaDeficit.logCutoff a (-2 * t) (-t)) z| ≤
          3 * (2 * Real.pi * ∫ u : ℝ,
            |AreaDeficit.transitionSecond u|) := by
  have hbound :=
    q.eventually_bounded_new_puncture_boundary_mass_explicit s hWN
      (mdifferentiableOn_subtypeRestr hUN hc) ha hR hball
  have heq := p.eventually_domainChart_boundary_eq_nested hVU hUN q W hW
    hWN s hc hR hball
  filter_upwards [hbound, heq] with t ht he
  rw [he]
  exact ht

end AreaDeficit.Surfaces.DiscCover

#print axioms AreaDeficit.Surfaces.DiscCover.tendsto_domainChart_old_boundary_mass_zero
#print axioms AreaDeficit.Surfaces.DiscCover.eventually_bounded_domainChart_new_boundary_mass

