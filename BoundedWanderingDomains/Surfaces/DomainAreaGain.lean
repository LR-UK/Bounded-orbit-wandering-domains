module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.DomainChartDensity
public import BoundedWanderingDomains.Surfaces.DensityRatioInvariance
public import BoundedWanderingDomains.Surfaces.AreaIntegration

@[expose] public section

/-! # Intrinsic area gain for possibly disconnected open subdomains

The componentwise density ratio weights the ambient intrinsic area measure.
The coordinate formula identifies this measure with the nonnegative part
of the difference of squared hyperbolic densities. No infinite areas are
subtracted, and no chart partition or component enumeration is chosen here.
-/
open Set Function Filter MeasureTheory
open scoped Manifold Topology ENNReal
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]

noncomputable def domainDensityRatio (p : DiscCover M) (U : TopologicalSpace.Opens M)
    (x : M) : ℝ := by
  classical
  exact if hx : x ∈ U then
    p.domainDensity U (chartAt ℂ x) ⟨x,hx⟩ / p.density (chartAt ℂ x) x else 0

theorem domainDensityRatio_eq (p : DiscCover M) (U : TopologicalSpace.Opens M)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {x : M} (hx : x ∈ U) (hxc : x ∈ c.source) :
    p.domainDensityRatio U x = p.domainDensity U c ⟨x,hx⟩ / p.density c x := by
  classical
  simp only [domainDensityRatio, dite_eq_left hx, domainDensity]
  exact p.density_ratio_coordinate_independent (p.componentCover U ⟨x,hx⟩)
    ⟨componentPoint U ⟨x,hx⟩⟩ (mdifferentiable_chart (I := 𝓘(ℂ)) x).1 hc
    (mem_chart_source ℂ x) hxc

theorem domainDensityRatio_chart (p : DiscCover M) (U : TopologicalSpace.Opens M)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {x : M} (hxc : x ∈ c.source) :
    p.domainDensityRatio U x = p.domainChartDensity U c (c x) / p.chartDensity c (c x) := by
  classical
  have he : p.chartDensity c (c x) = p.density c x := by
    change p.density c (c.symm (c x)) = _
    rw [c.left_inv hxc]
  rw [he]
  by_cases hx : x ∈ U
  · have hz : c x ∈ domainChartSet U c :=
      ⟨c.map_source hxc, by
        change c.symm (c x) ∈ U
        rw [c.left_inv hxc]
        exact hx⟩
    rw [p.domainDensityRatio_eq U hc hx hxc, p.domainChartDensity_of_mem U c hz]
    congr 2
    exact Subtype.ext (c.left_inv hxc).symm
  · have hz : c x ∉ domainChartSet U c := by
      intro h
      apply hx
      have hh : c.symm (c x) ∈ U := h.2
      rwa [c.left_inv hxc] at hh
    simp only [domainDensityRatio, dite_eq_right hx, domainChartDensity,
      dite_eq_right hz, zero_div]

theorem domainDensityRatio_continuousOn (p : DiscCover M) (U : TopologicalSpace.Opens M) :
    ContinuousOn (p.domainDensityRatio U) U := by
  intro x hx
  let c := chartAt ℂ x
  have hc := (mdifferentiable_chart (I := 𝓘(ℂ)) x).1
  have hxc : x ∈ c.source := mem_chart_source ℂ x
  have hzx : c x ∈ domainChartSet U c :=
    ⟨c.map_source hxc, by simpa only [mem_preimage,c.left_inv hxc] using hx⟩
  have hu := (p.domainChartDensity_contDiffAt U hc hzx).continuousAt.comp (c.continuousAt hxc)
  have hp := (p.chartDensity_contDiffAt hc (c.map_source hxc)).continuousAt.comp
    (c.continuousAt hxc)
  have hn := ne_of_gt (p.chartDensity_pos hc (c.map_source hxc))
  apply (hu.div hp hn).continuousWithinAt.congr_of_eventuallyEq
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (c.open_source.mem_nhds hxc)] with y hy
    exact p.domainDensityRatio_chart U hc hy
  · exact p.domainDensityRatio_chart U hc hxc

theorem domainDensityRatio_independent (p q : DiscCover M)
    (U : TopologicalSpace.Opens M) (x : M) :
    p.domainDensityRatio U x = q.domainDensityRatio U x := by
  classical
  by_cases hx : x ∈ U
  · let c := chartAt ℂ x
    have hc := (mdifferentiable_chart (I := 𝓘(ℂ)) x).1
    have hxc : x ∈ c.source := mem_chart_source ℂ x
    rw [p.domainDensityRatio_eq U hc hx hxc,q.domainDensityRatio_eq U hc hx hxc]
    dsimp only [domainDensity]
    have hs : componentPoint U ⟨x,hx⟩ ∈
        (c.subtypeRestr ⟨componentPoint U ⟨x,hx⟩⟩).source := by
      simpa only [OpenPartialHomeomorph.subtypeRestr_source,mem_preimage,componentPoint] using hxc
    rw [(p.componentCover U ⟨x,hx⟩).density_independent (q.componentCover U ⟨x,hx⟩)
      (mdifferentiableOn_subtypeRestr _ hc) hs,p.density_independent q hc hxc]
  · simp only [domainDensityRatio,dite_eq_right hx]

variable [MeasurableSpace M] [BorelSpace M]

theorem domainDensityRatio_measurable (p : DiscCover M) (U : TopologicalSpace.Opens M) :
    Measurable (p.domainDensityRatio U) := by
  classical
  have hm := (p.domainDensityRatio_continuousOn U).measurable_piecewise
    (g := fun _ => (0 : ℝ)) continuousOn_const U.isOpen.measurableSet
  have he : (U : Set M).piecewise (p.domainDensityRatio U) (fun _ => 0) =
      p.domainDensityRatio U := by
    funext x
    by_cases hx : x ∈ U
    · simp only [piecewise_eq_of_mem _ _ _ hx]
    · simp only [piecewise_eq_of_notMem _ _ _ hx,domainDensityRatio,dite_eq_right hx]
  rwa [he] at hm

noncomputable def domainAreaGain (p : DiscCover M) (U V : TopologicalSpace.Opens M) :
    Measure M := p.hyperbolicArea.withDensity (fun x => ENNReal.ofReal
      ((p.domainDensityRatio V x)^2 - (p.domainDensityRatio U x)^2))

theorem domainAreaGain_independent (p q : DiscCover M) (U V : TopologicalSpace.Opens M) :
    p.domainAreaGain U V = q.domainAreaGain U V := by
  unfold domainAreaGain
  rw [p.hyperbolicArea_independent q]
  congr 1
  funext x
  rw [p.domainDensityRatio_independent q U x,p.domainDensityRatio_independent q V x]

theorem domainAreaGain_compl (p : DiscCover M) (U V : TopologicalSpace.Opens M) :
    p.domainAreaGain U V (V : Set M)ᶜ = 0 := by
  classical
  rw [domainAreaGain,withDensity_apply _ V.isOpen.measurableSet.compl]
  calc
    (∫⁻ x in (V : Set M)ᶜ, ENNReal.ofReal
        ((p.domainDensityRatio V x)^2 - (p.domainDensityRatio U x)^2) ∂p.hyperbolicArea) =
        ∫⁻ _ in (V : Set M)ᶜ, (0 : ℝ≥0∞) ∂p.hyperbolicArea := by
      apply setLIntegral_congr_fun V.isOpen.measurableSet.compl
      intro x hx
      have hxV : x ∉ V := hx
      have he : p.domainDensityRatio V x = 0 := by
        simp only [domainDensityRatio,dite_eq_right hxV]
      dsimp only
      rw [he,zero_pow (by decide),zero_sub]
      exact ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr (sq_nonneg _))
    _ = 0 := by simp

theorem domainAreaGain_inter (p : DiscCover M) (U V : TopologicalSpace.Opens M)
    (A : Set M) : p.domainAreaGain U V (A ∩ V) = p.domainAreaGain U V A :=
  measure_inter_conull (p.domainAreaGain_compl U V)

theorem domainAreaGain_coordinate_formula (p : DiscCover M)
    (U V : TopologicalSpace.Opens M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {A : Set M} (hA : MeasurableSet A) (hAc : A ⊆ c.source) :
    p.domainAreaGain U V A = ∫⁻ z in c '' A, ENNReal.ofReal
      ((p.domainChartDensity V c z)^2 - (p.domainChartDensity U c z)^2) := by
  have hm : Measurable (fun x => ENNReal.ofReal
      ((p.domainDensityRatio V x)^2 - (p.domainDensityRatio U x)^2)) :=
    (((p.domainDensityRatio_measurable V).pow_const 2).sub
      ((p.domainDensityRatio_measurable U).pow_const 2)).ennreal_ofReal
  rw [domainAreaGain,withDensity_apply _ hA,p.hyperbolicArea_setLIntegral hc hA hAc hm]
  apply setLIntegral_congr_fun
    (chart_image_measurable c (p.projection ⟨0,by simp [unitDisc]⟩) hA hAc)
  rintro z ⟨x,hx,rfl⟩
  dsimp only
  rw [c.left_inv (hAc hx),p.domainDensityRatio_chart U hc (hAc hx),
    p.domainDensityRatio_chart V hc (hAc hx),← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  have hn := ne_of_gt (p.chartDensity_pos hc (c.map_source (hAc hx)))
  field_simp

end AreaDeficit.Surfaces.DiscCover
