module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.AreaIntegration

@[expose] public section
open Set Function Filter Metric MeasureTheory
open scoped Manifold Topology ENNReal
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]

/-- Intrinsic hyperbolic area has exactly the usual chart-area null sets. -/
theorem hyperbolicArea_zero_iff_chart (p : DiscCover M)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {A : Set M} (hA : MeasurableSet A) (hAc : A ⊆ c.source) :
    p.hyperbolicArea A = 0 ↔ volume (c '' A) = 0 := by
  rw [p.hyperbolicArea_apply_chart hc hA hAc]
  unfold coordinateArea
  have hsub : c '' A ⊆ c.target := by
    rintro z ⟨x,hx,rfl⟩
    exact c.map_source (hAc hx)
  have hm := chart_image_measurable c (p.projection ⟨0,by simp [unitDisc]⟩) hA hAc
  have hf := (p.chartDensity_sq_aemeasurable hc).mono_measure
    (Measure.restrict_mono hsub le_rfl)
  rw [setLIntegral_eq_zero_iff' hm hf]
  constructor
  · intro h
    have he : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ c '' A := by
      filter_upwards [h] with z hz hzA
      have hp : 0 < ENNReal.ofReal ((p.chartDensity c z)^2) :=
        ENNReal.ofReal_pos.mpr (sq_pos_of_pos (p.chartDensity_pos hc (hsub hzA)))
      exact (ne_of_gt hp) (hz hzA)
    simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using he
  · intro h
    filter_upwards [show ∀ᵐ z ∂(volume : Measure ℂ), z ∉ c '' A from by
      simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using h] with z hz
    exact fun hmem => (hz hmem).elim

theorem hyperbolicArea_pos_iff_chart (p : DiscCover M)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {A : Set M} (hA : MeasurableSet A) (hAc : A ⊆ c.source) :
    0 < p.hyperbolicArea A ↔ 0 < volume (c '' A) := by
  rw [pos_iff_ne_zero,pos_iff_ne_zero]
  exact not_congr (p.hyperbolicArea_zero_iff_chart hc hA hAc)
end AreaDeficit.Surfaces.DiscCover
