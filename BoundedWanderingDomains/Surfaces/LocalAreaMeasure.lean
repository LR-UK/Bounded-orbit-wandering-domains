/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.ChartArea
import Mathlib.MeasureTheory.Measure.WithDensity
open Set Function Filter Metric MeasureTheory
open scoped Manifold Topology ENNReal
namespace AreaDeficit.Surfaces
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
noncomputable def chartInverseExtension (c : OpenPartialHomeomorph M ℂ) (x₀ : M) : ℂ → M := by
  classical
  exact c.target.piecewise c.symm (fun _ => x₀)
omit [IsManifold 𝓘(ℂ) 1 M] [ChartedSpace ℂ M] in
theorem chartInverseExtension_measurable (c : OpenPartialHomeomorph M ℂ) (x₀ : M) :
    Measurable (chartInverseExtension c x₀) := by
  classical
  exact c.continuousOn_symm.measurable_piecewise continuousOn_const c.open_target.measurableSet
omit [IsManifold 𝓘(ℂ) 1 M] [ChartedSpace ℂ M] [MeasurableSpace M] [BorelSpace M] in
theorem chartInverseExtension_eq (c : OpenPartialHomeomorph M ℂ) (x₀ : M)
    {z : ℂ} (hz : z ∈ c.target) : chartInverseExtension c x₀ z = c.symm z := by
  classical
  exact piecewise_eq_of_mem _ _ _ hz
omit [IsManifold 𝓘(ℂ) 1 M] [ChartedSpace ℂ M] in
theorem chart_image_measurable (c : OpenPartialHomeomorph M ℂ) (x₀ : M)
    {A : Set M} (hA : MeasurableSet A) (hAc : A ⊆ c.source) :
    MeasurableSet (c '' A) := by
  have he := chartInverseExtension_measurable c x₀
  have hset : c '' A = c.target ∩ (chartInverseExtension c x₀) ⁻¹' A := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨c.map_source (hAc hx),?_⟩
      change chartInverseExtension c x₀ (c x) ∈ A
      rw [chartInverseExtension_eq c x₀ (c.map_source (hAc hx)),c.left_inv (hAc hx)]
      exact hx
    · rintro ⟨hz,hzA⟩
      change chartInverseExtension c x₀ z ∈ A at hzA
      rw [chartInverseExtension_eq c x₀ hz] at hzA
      exact ⟨c.symm z,hzA,c.right_inv hz⟩
  rw [hset]
  exact c.open_target.measurableSet.inter (he hA)
namespace DiscCover
noncomputable def localArea (p : DiscCover M) (c : OpenPartialHomeomorph M ℂ) : Measure M :=
  Measure.map (chartInverseExtension c (p.projection ⟨0,by simp [unitDisc]⟩))
    ((volume.restrict c.target).withDensity (fun z => ENNReal.ofReal ((p.chartDensity c z)^2)))
theorem localArea_apply (p : DiscCover M) (c : OpenPartialHomeomorph M ℂ)
    {A : Set M} (hA : MeasurableSet A) :
    p.localArea c A = p.coordinateArea c (A ∩ c.source) := by
  let x₀ := p.projection ⟨0,by simp [unitDisc]⟩
  let e := chartInverseExtension c x₀
  have he : Measurable e := chartInverseExtension_measurable c x₀
  have hpre : MeasurableSet (e ⁻¹' A) := he hA
  change Measure.map e _ A = _
  rw [Measure.map_apply he hA, withDensity_apply _ hpre]
  rw [Measure.restrict_restrict hpre]
  have hset : e ⁻¹' A ∩ c.target = c '' (A ∩ c.source) := by
    ext z
    constructor
    · rintro ⟨hzA,hz⟩
      have hez : e z = c.symm z := chartInverseExtension_eq c x₀ hz
      refine ⟨c.symm z,⟨?_,c.map_target hz⟩,c.right_inv hz⟩
      simpa only [mem_preimage, hez] using hzA
    · rintro ⟨x,⟨hxA,hx⟩,rfl⟩
      refine ⟨?_,c.map_source hx⟩
      change e (c x) ∈ A
      rw [show e (c x) = c.symm (c x) from chartInverseExtension_eq c x₀ (c.map_source hx),
        c.left_inv hx]
      exact hxA
  rw [hset]
  rfl
theorem localArea_apply_of_subset (p : DiscCover M) (c : OpenPartialHomeomorph M ℂ)
    {A : Set M} (hA : MeasurableSet A) (hAc : A ⊆ c.source) :
    p.localArea c A = p.coordinateArea c A := by
  rw [p.localArea_apply c hA, inter_eq_left.mpr hAc]
theorem localArea_overlap (p : DiscCover M) {c d : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {A : Set M} (hA : MeasurableSet A) (hAc : A ⊆ c.source) (hAd : A ⊆ d.source) :
    p.localArea c A = p.localArea d A := by
  rw [p.localArea_apply_of_subset c hA hAc,p.localArea_apply_of_subset d hA hAd]
  exact (p.coordinateArea_eq hc hd hAc hAd
    (chart_image_measurable c (p.projection ⟨0,by simp [unitDisc]⟩) hA hAc)).symm

theorem localArea_cover_independent (p q : DiscCover M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source) :
    p.localArea c = q.localArea c := by
  apply Measure.ext
  intro A hA
  rw [p.localArea_apply c hA,q.localArea_apply c hA]
  unfold coordinateArea
  apply setLIntegral_congr_fun
    (chart_image_measurable c (p.projection ⟨0,by simp [unitDisc]⟩)
      (hA.inter c.open_source.measurableSet) inter_subset_right)
  rintro z ⟨x,⟨_,hx⟩,rfl⟩
  change ENNReal.ofReal ((p.density c (c.symm (c x)))^2) =
    ENNReal.ofReal ((q.density c (c.symm (c x)))^2)
  rw [c.left_inv hx,p.density_independent q hc hx]
end DiscCover
end AreaDeficit.Surfaces
