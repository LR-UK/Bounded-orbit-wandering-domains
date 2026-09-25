/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DomainAreaGain
import BoundedWanderingDomains.Surfaces.DomainSchwarz

/-! # Localisation and telescoping inequalities for intrinsic area gain -/
open Set Function Filter MeasureTheory
open scoped Manifold Topology ENNReal
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]

theorem domainDensityRatio_nonneg (p : DiscCover M)
    (U : TopologicalSpace.Opens M) (x : M) : 0 ≤ p.domainDensityRatio U x := by
  classical
  by_cases hx : x ∈ U
  · rw [p.domainDensityRatio_eq U (mdifferentiable_chart (I := 𝓘(ℂ)) x).1 hx
      (mem_chart_source ℂ x)]
    exact div_nonneg (p.domainDensity_pos U (mdifferentiable_chart (I := 𝓘(ℂ)) x).1
      (mem_chart_source ℂ x)).le
      (p.density_pos (mdifferentiable_chart (I := 𝓘(ℂ)) x).1 (mem_chart_source ℂ x)).le
  · simp only [domainDensityRatio,dite_eq_right hx,le_refl]

theorem domainDensityRatio_mono (p : DiscCover M)
    {U V : TopologicalSpace.Opens M} (hVU : V ≤ U) {x : M} (hx : x ∈ V) :
    p.domainDensityRatio U x ≤ p.domainDensityRatio V x := by
  have hc := (mdifferentiable_chart (I := 𝓘(ℂ)) x).1
  have hxc := mem_chart_source ℂ x
  rw [p.domainDensityRatio_eq U hc (hVU hx) hxc,p.domainDensityRatio_eq V hc hx hxc]
  exact div_le_div_of_nonneg_right (p.domainDensity_mono hVU hc (x := ⟨x,hx⟩) hxc)
    (p.density_pos hc hxc).le

variable [MeasurableSpace M] [BorelSpace M]

@[simp] theorem domainAreaGain_self (p : DiscCover M) (U : TopologicalSpace.Opens M) :
    p.domainAreaGain U U = 0 := by
  simp only [domainAreaGain,sub_self,ENNReal.ofReal_zero]
  exact withDensity_zero

/-- A pointwise localisation inequality, valid even if the measured set
meets the old complement. The intermediate domain need not be connected. -/
theorem domainAreaGain_localize (p : DiscCover M)
    (U V W Z : TopologicalSpace.Opens M) (hZV : Z ≤ V)
    {E : Set M} (hE : MeasurableSet E) (hEZ : E ∩ V ⊆ Z) :
    p.domainAreaGain U V E ≤ p.domainAreaGain U W E + p.domainAreaGain W Z E := by
  have hm : Measurable (fun x => ENNReal.ofReal
      ((p.domainDensityRatio W x)^2 - (p.domainDensityRatio U x)^2)) :=
    (((p.domainDensityRatio_measurable W).pow_const 2).sub
      ((p.domainDensityRatio_measurable U).pow_const 2)).ennreal_ofReal
  simp only [domainAreaGain,withDensity_apply _ hE]
  rw [← lintegral_add_left hm]
  apply setLIntegral_mono' hE
  intro x hx
  by_cases hxV : x ∈ V
  · have hxZ := hEZ ⟨hx,hxV⟩
    have hmV := p.domainDensityRatio_mono hZV hxZ
    have hnV := p.domainDensityRatio_nonneg V x
    have hnZ := p.domainDensityRatio_nonneg Z x
    calc
      ENNReal.ofReal ((p.domainDensityRatio V x)^2 - (p.domainDensityRatio U x)^2) ≤
          ENNReal.ofReal (((p.domainDensityRatio W x)^2 - (p.domainDensityRatio U x)^2) +
            ((p.domainDensityRatio Z x)^2 - (p.domainDensityRatio W x)^2)) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith
      _ ≤ _ := ENNReal.ofReal_add_le
  · have he : p.domainDensityRatio V x = 0 := by
      simp only [domainDensityRatio,dite_eq_right hxV]
    rw [he,zero_pow (by decide),zero_sub,ENNReal.ofReal_eq_zero.mpr
      (neg_nonpos.mpr (sq_nonneg _))]
    exact zero_le

/-- Telescoping gain is subadditive without subtracting infinite areas. -/
theorem domainAreaGain_triangle (p : DiscCover M)
    (U V W : TopologicalSpace.Opens M) {E : Set M} (hE : MeasurableSet E) :
    p.domainAreaGain U V E ≤ p.domainAreaGain U W E + p.domainAreaGain W V E :=
  p.domainAreaGain_localize U V W V le_rfl hE inter_subset_right

end AreaDeficit.Surfaces.DiscCover
