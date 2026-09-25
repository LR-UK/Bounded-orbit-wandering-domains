/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.Surfaces.DensityRatioContinuity
import BoundedWanderingDomains.Surfaces.AreaIntegration

/-! # Intrinsic area gain without subtraction of infinite total areas -/
open Set Function Filter Metric MeasureTheory
open scoped Manifold Topology ENNReal
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

/-- Fraction of the smaller-domain area contributed by the metric increase. -/
noncomputable def gainWeight (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (x : U) : ℝ := 1 - (p.densityRatio q x)⁻¹ ^ 2

theorem gainWeight_bounds (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (x : U) : 0 ≤ p.gainWeight q x ∧ p.gainWeight q x ≤ 1 := by
  have hr := p.one_le_densityRatio q x
  have hp : 0 < p.densityRatio q x := lt_of_lt_of_le zero_lt_one hr
  have hi : 0 ≤ (p.densityRatio q x)⁻¹ := inv_nonneg.mpr hp.le
  have hi1 : (p.densityRatio q x)⁻¹ ≤ 1 := by
    rw [← one_div]
    exact (div_le_one hp).mpr hr
  unfold gainWeight
  constructor <;> nlinarith [sq_nonneg ((p.densityRatio q x)⁻¹)]

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

theorem gainWeight_measurable (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) : Measurable (p.gainWeight q) :=
  measurable_const.sub (((p.densityRatio_measurable q).inv).pow_const 2)

/-- The intrinsic nonnegative area-gain measure. It is meaningful even when
both original and new total areas are infinite. -/
noncomputable def areaGain (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) : Measure U :=
  q.hyperbolicArea.withDensity (fun x => ENNReal.ofReal (p.gainWeight q x))

theorem areaGain_apply (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) {A : Set U} (hA : MeasurableSet A) :
    p.areaGain q A = ∫⁻ x in A, ENNReal.ofReal (p.gainWeight q x) ∂q.hyperbolicArea :=
  withDensity_apply _ hA

/-- In a chart, intrinsic area gain is exactly the integral of the difference
of squared densities. No subtraction of total areas occurs. -/
theorem areaGain_coordinate_formula (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (hU : Nonempty U) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {A : Set U} (hA : MeasurableSet A) (hAc : A ⊆ (c.subtypeRestr hU).source) :
    p.areaGain q A = ∫⁻ z in (c.subtypeRestr hU) '' A,
      ENNReal.ofReal ((q.chartDensity (c.subtypeRestr hU) z)^2 -
        (p.chartDensity c z)^2) := by
  let d := c.subtypeRestr hU
  have hd := mdifferentiableOn_subtypeRestr hU hc
  rw [p.areaGain_apply q hA,q.hyperbolicArea_setLIntegral hd hA hAc
    (p.gainWeight_measurable q).ennreal_ofReal]
  apply setLIntegral_congr_fun (chart_image_measurable d
    (q.projection ⟨0,by simp [unitDisc]⟩) hA hAc)
  rintro z ⟨x,hx,rfl⟩
  have hxd := hAc hx
  have hxc : (x : M) ∈ c.source := by
    simpa only [OpenPartialHomeomorph.subtypeRestr_source,mem_preimage] using hxd
  have hqpos := q.density_pos hd hxd
  have hpval : p.chartDensity c (d x) = p.density c x := by
    change p.density c (c.symm (c x)) = p.density c x
    rw [c.left_inv hxc]
  have hqval : q.chartDensity d (d x) = q.density d x := by
    change q.density d (d.symm (d x)) = q.density d x
    rw [d.left_inv hxd]
  dsimp only
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  change (q.chartDensity d (d x))^2 * p.gainWeight q (d.symm (d x)) =
    (q.chartDensity d (d x))^2 - (p.chartDensity c (d x))^2
  rw [d.left_inv hxd,hpval,hqval]
  unfold gainWeight
  rw [p.densityRatio_eq q hU hc hxc,inv_div]
  have hqn : q.density d x ≠ 0 := ne_of_gt hqpos
  change (q.density d x)^2 * (1 - (p.density c x / q.density d x)^2) = _
  field_simp
  <;> ring

end AreaDeficit.Surfaces.DiscCover
