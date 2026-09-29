module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.Surfaces.HyperbolicArea
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! # Integration of scalar functions against intrinsic hyperbolic area -/
open Set Function Filter Metric MeasureTheory
open scoped Manifold Topology ENNReal
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
theorem chartDensity_sq_aemeasurable (p : DiscCover M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source) :
    AEMeasurable (fun z => ENNReal.ofReal ((p.chartDensity c z)^2))
      (volume.restrict c.target) := by
  have hcont : ContinuousOn (p.chartDensity c) c.target :=
    fun z hz => (p.chartDensity_contDiffAt hc hz).continuousAt.continuousWithinAt
  exact (ENNReal.continuous_ofReal.comp_continuousOn (hcont.pow 2)).aemeasurable c.open_target.measurableSet

theorem localArea_setLIntegral (p : DiscCover M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {A : Set M} (hA : MeasurableSet A) (hAc : A ⊆ c.source)
    {b : M → ℝ≥0∞} (hb : Measurable b) :
    (∫⁻ x in A, b x ∂p.localArea c) =
      ∫⁻ z in c '' A, ENNReal.ofReal ((p.chartDensity c z)^2) * b (c.symm z) := by
  let x₀ := p.projection ⟨0,by simp [unitDisc]⟩
  let e := chartInverseExtension c x₀
  have he : Measurable e := chartInverseExtension_measurable c x₀
  change (∫⁻ x in A, b x ∂Measure.map e _) = _
  rw [setLIntegral_map hA hb he]
  change (∫⁻ x in e ⁻¹' A, (b ∘ e) x ∂(volume.restrict c.target).withDensity
    (fun z => ENNReal.ofReal ((p.chartDensity c z)^2))) = _
  rw [setLIntegral_withDensity_eq_lintegral_mul₀ (p.chartDensity_sq_aemeasurable hc)
      ((hb.comp he).aemeasurable) (he hA),Measure.restrict_restrict (he hA)]
  have hset : e ⁻¹' A ∩ c.target = c '' A := by
    ext z
    constructor
    · rintro ⟨hzA,hz⟩
      change e z ∈ A at hzA
      rw [show e z = c.symm z from chartInverseExtension_eq c x₀ hz] at hzA
      exact ⟨c.symm z,hzA,c.right_inv hz⟩
    · rintro ⟨x,hx,rfl⟩
      refine ⟨?_,c.map_source (hAc hx)⟩
      change e (c x) ∈ A
      rw [show e (c x) = c.symm (c x) from chartInverseExtension_eq c x₀ (c.map_source (hAc hx)),
        c.left_inv (hAc hx)]
      exact hx
  rw [hset]
  apply setLIntegral_congr_fun (chart_image_measurable c x₀ hA hAc)
  rintro z ⟨x,hx,rfl⟩
  dsimp only [Pi.mul_apply,Function.comp_apply]
  rw [show e (c x) = c.symm (c x) from chartInverseExtension_eq c x₀ (c.map_source (hAc hx))]

variable [SecondCountableTopology M]

theorem hyperbolicArea_restrict_chart (p : DiscCover M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source) :
    p.hyperbolicArea.restrict c.source = p.localArea c := by
  apply Measure.ext
  intro A hA
  rw [Measure.restrict_apply hA,
    p.hyperbolicArea_apply_chart hc (hA.inter c.open_source.measurableSet) inter_subset_right,
    p.localArea_apply c hA]

theorem hyperbolicArea_setLIntegral (p : DiscCover M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {A : Set M} (hA : MeasurableSet A) (hAc : A ⊆ c.source)
    {b : M → ℝ≥0∞} (hb : Measurable b) :
    (∫⁻ x in A, b x ∂p.hyperbolicArea) =
      ∫⁻ z in c '' A, ENNReal.ofReal ((p.chartDensity c z)^2) * b (c.symm z) := by
  have he : p.hyperbolicArea.restrict A = (p.localArea c).restrict A := by
    rw [← p.hyperbolicArea_restrict_chart hc,Measure.restrict_restrict_of_subset hAc]
  change (∫⁻ x, b x ∂p.hyperbolicArea.restrict A) = _
  rw [he]
  exact p.localArea_setLIntegral hc hA hAc hb

/-- Signed integral form of the chart formula on the full chart source. -/
theorem hyperbolicArea_setIntegral_chart_source
    (p : DiscCover M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {b : M → ℝ} (hb : Measurable b) :
    (∫ x in c.source, b x ∂p.hyperbolicArea) =
      ∫ z in c.target, (p.chartDensity c z) ^ 2 * b (c.symm z) := by
  let x₀ := p.projection ⟨0, by simp [unitDisc]⟩
  let e := chartInverseExtension c x₀
  let w : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal ((p.chartDensity c z) ^ 2)
  have he : Measurable e := chartInverseExtension_measurable c x₀
  have hw : AEMeasurable w (volume.restrict c.target) :=
    p.chartDensity_sq_aemeasurable hc
  have hwtop : ∀ᵐ z ∂volume.restrict c.target, w z < ⊤ := by
    filter_upwards with z
    exact ENNReal.ofReal_lt_top
  change (∫ x, b x ∂p.hyperbolicArea.restrict c.source) = _
  rw [p.hyperbolicArea_restrict_chart hc]
  change (∫ x, b x ∂Measure.map e
    ((volume.restrict c.target).withDensity w)) = _
  rw [integral_map he.aemeasurable hb.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul₀ hw hwtop]
  change (∫ z in c.target, (w z).toReal * b (e z)) = _
  apply setIntegral_congr_fun c.open_target.measurableSet
  intro z hz
  dsimp only
  rw [show e z = c.symm z from chartInverseExtension_eq c x₀ hz]
  simp [w, ENNReal.toReal_ofReal (sq_nonneg (p.chartDensity c z))]

end AreaDeficit.Surfaces.DiscCover
