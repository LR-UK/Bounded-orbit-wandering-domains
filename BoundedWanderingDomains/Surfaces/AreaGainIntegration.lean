module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.AreaGain

@[expose] public section

/-! # Integration against intrinsic hyperbolic area gain -/

open Set Function MeasureTheory
open scoped Manifold Topology ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]

/-- Weighted coordinate formula for intrinsic area gain.  This is the
function-valued version of `areaGain_coordinate_formula`. -/
theorem areaGain_setLIntegral_coordinate_formula
    (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (hU : Nonempty U) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {A : Set U} (hA : MeasurableSet A)
    (hAc : A ⊆ (c.subtypeRestr hU).source)
    {b : U → ℝ≥0∞} (hb : Measurable b) :
    (∫⁻ x in A, b x ∂p.areaGain q) =
      ∫⁻ z in (c.subtypeRestr hU) '' A,
        ENNReal.ofReal ((q.chartDensity (c.subtypeRestr hU) z)^2 -
          (p.chartDensity c z)^2) * b ((c.subtypeRestr hU).symm z) := by
  let d := c.subtypeRestr hU
  have hd := mdifferentiableOn_subtypeRestr hU hc
  change (∫⁻ x in A, b x ∂q.hyperbolicArea.withDensity
    (fun x => ENNReal.ofReal (p.gainWeight q x))) = _
  rw [setLIntegral_withDensity_eq_lintegral_mul₀
    (p.gainWeight_measurable q).ennreal_ofReal.aemeasurable hb.aemeasurable hA]
  rw [q.hyperbolicArea_setLIntegral hd hA hAc
    ((p.gainWeight_measurable q).ennreal_ofReal.mul hb)]
  apply setLIntegral_congr_fun (chart_image_measurable d
    (q.projection ⟨0, by simp [unitDisc]⟩) hA hAc)
  rintro z ⟨x, hx, rfl⟩
  have hxd : x ∈ d.source := hAc hx
  have hxc : (x : M) ∈ c.source := by
    simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hxd
  have hqpos := q.density_pos hd hxd
  have hpval : p.chartDensity c (d x) = p.density c x := by
    change p.density c (c.symm (c x)) = p.density c x
    rw [c.left_inv hxc]
  have hqval : q.chartDensity d (d x) = q.density d x := by
    change q.density d (d.symm (d x)) = q.density d x
    rw [d.left_inv hxd]
  dsimp only [Pi.mul_apply, Function.comp_apply]
  rw [← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  rw [d.left_inv hxd]
  rw [hpval, hqval]
  unfold gainWeight
  rw [p.densityRatio_eq q hU hc hxc, inv_div]
  have hqn : q.density d x ≠ 0 := ne_of_gt hqpos
  change (q.density d x)^2 * (1 - (p.density c x / q.density d x)^2) = _
  field_simp

end AreaDeficit.Surfaces.DiscCover
