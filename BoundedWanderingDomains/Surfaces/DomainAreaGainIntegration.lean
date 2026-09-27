/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DomainAreaGain

/-! # Integration against ambient domain-area gain -/

open Set Function MeasureTheory
open scoped Manifold Topology ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]

/-- Weighted coordinate formula for componentwise domain-area gain.  This
is the function-valued version of `domainAreaGain_coordinate_formula` and
allows one fixed ambient partition of unity to be used for every finite
puncture model. -/
theorem domainAreaGain_setLIntegral_coordinate_formula
    (p : DiscCover M) (U V : TopologicalSpace.Opens M)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {A : Set M} (hA : MeasurableSet A) (hAc : A ⊆ c.source)
    {b : M → ℝ≥0∞} (hb : Measurable b) :
    (∫⁻ x in A, b x ∂p.domainAreaGain U V) =
      ∫⁻ z in c '' A,
        ENNReal.ofReal ((p.domainChartDensity V c z)^2 -
          (p.domainChartDensity U c z)^2) * b (c.symm z) := by
  have hm : Measurable (fun x => ENNReal.ofReal
      ((p.domainDensityRatio V x)^2 - (p.domainDensityRatio U x)^2)) :=
    (((p.domainDensityRatio_measurable V).pow_const 2).sub
      ((p.domainDensityRatio_measurable U).pow_const 2)).ennreal_ofReal
  change (∫⁻ x in A, b x ∂p.hyperbolicArea.withDensity
    (fun x => ENNReal.ofReal
      ((p.domainDensityRatio V x)^2 - (p.domainDensityRatio U x)^2))) = _
  rw [setLIntegral_withDensity_eq_lintegral_mul₀
    hm.aemeasurable hb.aemeasurable hA]
  rw [p.hyperbolicArea_setLIntegral hc hA hAc (hm.mul hb)]
  apply setLIntegral_congr_fun (chart_image_measurable c
    (p.projection ⟨0, by simp [unitDisc]⟩) hA hAc)
  rintro z ⟨x, hx, rfl⟩
  have hxc : x ∈ c.source := hAc hx
  have hpval : p.chartDensity c (c x) = p.density c x := by
    change p.density c (c.symm (c x)) = p.density c x
    rw [c.left_inv hxc]
  dsimp only [Pi.mul_apply, Function.comp_apply]
  rw [← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  rw [c.left_inv hxc, p.domainDensityRatio_chart U hc hxc,
    p.domainDensityRatio_chart V hc hxc, hpval]
  have hpn : p.density c x ≠ 0 :=
    ne_of_gt (p.density_pos hc hxc)
  field_simp

end AreaDeficit.Surfaces.DiscCover

#print axioms AreaDeficit.Surfaces.DiscCover.domainAreaGain_setLIntegral_coordinate_formula
