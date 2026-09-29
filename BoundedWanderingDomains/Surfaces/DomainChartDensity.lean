module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.ComponentDensity

@[expose] public section

/-! # Regular and measurable chart densities on disconnected domains -/
open Set Function Filter
open scoped Manifold Topology ContDiff
namespace AreaDeficit.Surfaces
variable {M : Type*} [TopologicalSpace M]

def domainChartSet (U : TopologicalSpace.Opens M) (c : OpenPartialHomeomorph M ℂ) : Set ℂ :=
  c.target ∩ c.symm ⁻¹' (U : Set M)

theorem isOpen_domainChartSet (U : TopologicalSpace.Opens M)
    (c : OpenPartialHomeomorph M ℂ) : IsOpen (domainChartSet U c) :=
  c.isOpen_inter_preimage_symm U.isOpen

namespace DiscCover
variable [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M]
  [T2Space M] [SecondCountableTopology M]

/-- The componentwise chart density, extended by zero off its coordinate
domain. The zero extension is measurable; smoothness is asserted inside. -/
noncomputable def domainChartDensity (p : DiscCover M) (U : TopologicalSpace.Opens M)
    (c : OpenPartialHomeomorph M ℂ) (z : ℂ) : ℝ := by
  classical
  exact if hz : z ∈ domainChartSet U c then
    p.domainDensity U c ⟨c.symm z, hz.2⟩ else 0

theorem domainChartDensity_of_mem (p : DiscCover M) (U : TopologicalSpace.Opens M)
    (c : OpenPartialHomeomorph M ℂ) {z : ℂ} (hz : z ∈ domainChartSet U c) :
    p.domainChartDensity U c z = p.domainDensity U c ⟨c.symm z,hz.2⟩ := by
  simp only [domainChartDensity, dite_eq_left hz]

theorem domainChartDensity_local_eq (p : DiscCover M) (U : TopologicalSpace.Opens M)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {z : ℂ} (hz : z ∈ domainChartSet U c) :
    ∃ (V : TopologicalSpace.Opens M) (q : DiscCover V) (hV : Nonempty V),
      z ∈ (c.subtypeRestr hV).target ∧
      p.domainChartDensity U c =ᶠ[𝓝 z] q.chartDensity (c.subtypeRestr hV) := by
  let x : U := ⟨c.symm z,hz.2⟩
  let V := componentDomain U (x : M)
  let q := p.componentCover U x
  let hV : Nonempty V := ⟨componentPoint U x⟩
  let d := c.subtypeRestr hV
  have hzd : z ∈ d.target := by
    have h := c.map_subtype_source hV (x := componentPoint U x)
      (show (componentPoint U x : M) ∈ c.source from c.map_target hz.1)
    change c (c.symm z) ∈ d.target at h
    rwa [c.right_inv hz.1] at h
  refine ⟨V,q,hV,hzd,?_⟩
  filter_upwards [d.open_target.mem_nhds hzd] with t ht
  have htc : t ∈ c.target := c.subtypeRestr_target_subset hV ht
  have he : ((d.symm t : V) : M) = c.symm t := c.subtypeRestr_symm_apply hV ht
  have htV : c.symm t ∈ V := he ▸ (d.symm t).property
  have htU : c.symm t ∈ U := componentDomain_le U (x : M) htV
  rw [p.domainChartDensity_of_mem U c ⟨htc,htU⟩,
    p.domainDensity_eq_on_component U x ⟨c.symm t,htU⟩ htV q hc (c.map_target htc)]
  change q.density d ⟨c.symm t,htV⟩ = q.density d (d.symm t)
  congr 1
  exact Subtype.ext he.symm

theorem domainChartDensity_contDiffAt (p : DiscCover M) (U : TopologicalSpace.Opens M)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {z : ℂ} (hz : z ∈ domainChartSet U c) :
    ContDiffAt ℝ 2 (p.domainChartDensity U c) z := by
  obtain ⟨V,q,hV,hzV,he⟩ := p.domainChartDensity_local_eq U hc hz
  exact (q.chartDensity_contDiffAt (mdifferentiableOn_subtypeRestr hV hc) hzV).congr_of_eventuallyEq he

theorem domainChartDensity_pos (p : DiscCover M) (U : TopologicalSpace.Opens M)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {z : ℂ} (hz : z ∈ domainChartSet U c) :
    0 < p.domainChartDensity U c z := by
  rw [p.domainChartDensity_of_mem U c hz]
  exact p.domainDensity_pos U hc (c.map_target hz.1)

theorem domainChartDensity_curvature (p : DiscCover M) (U : TopologicalSpace.Opens M)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {z : ℂ} (hz : z ∈ domainChartSet U c) :
    Laplacian.laplacian (fun t => Real.log (p.domainChartDensity U c t)) z =
      (p.domainChartDensity U c z)^2 := by
  obtain ⟨V,q,hV,hzV,he⟩ := p.domainChartDensity_local_eq U hc hz
  have hlog := he.fun_comp Real.log
  simp only [Function.comp_def] at hlog
  rw [(InnerProductSpace.laplacian_congr_nhds hlog).eq_of_nhds, he.eq_of_nhds]
  exact q.chartDensity_curvature (mdifferentiableOn_subtypeRestr hV hc) hzV

theorem domainChartDensity_measurable (p : DiscCover M) (U : TopologicalSpace.Opens M)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source) :
    Measurable (p.domainChartDensity U c) := by
  classical
  have hcont : ContinuousOn (p.domainChartDensity U c) (domainChartSet U c) :=
    fun z hz => (p.domainChartDensity_contDiffAt U hc hz).continuousAt.continuousWithinAt
  have hm := hcont.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const
    (isOpen_domainChartSet U c).measurableSet
  have he : (domainChartSet U c).piecewise (p.domainChartDensity U c) (fun _ => 0) =
      p.domainChartDensity U c := by
    funext z
    by_cases hz : z ∈ domainChartSet U c
    · simp only [piecewise_eq_of_mem _ _ _ hz]
    · simp only [piecewise_eq_of_notMem _ _ _ hz, domainChartDensity, dite_eq_right hz]
  rwa [he] at hm

end DiscCover
end AreaDeficit.Surfaces
