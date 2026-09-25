/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DomainArea
import BoundedWanderingDomains.Surfaces.DomainDensityDivergence
import BoundedWanderingDomains.Surfaces.HyperbolicAreaFinite
import BoundedWanderingDomains.AreaCancellation

/-! # Intrinsic area divergence on the limiting closed complement -/
open Set Function Filter MeasureTheory
open scoped Manifold Topology ENNReal
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]

theorem domainAreaWeight_tendsto_top (p : DiscCover M)
    (P : ℕ → Finset M) (hP : Monotone P) {x : M}
    (hxP : ∀ n, x ∉ P n) (hx : x ∈ closure (⋃ n, (P n : Set M))) :
    Tendsto (fun n => ENNReal.ofReal ((p.domainDensityRatio (finitePunctureDomain (P n)) x)^2))
      atTop (𝓝 ⊤) := by
  let c := chartAt ℂ x
  have hc := (mdifferentiable_chart (I := 𝓘(ℂ)) x).1
  have hxc := mem_chart_source ℂ x
  have hρ := p.domainDensity_tendsto_atTop_finite_punctures P hP hc hxc hxP hx
  have hr : Tendsto (fun n => p.domainDensityRatio (finitePunctureDomain (P n)) x)
      atTop atTop := by
    have he (n : ℕ) := p.domainDensityRatio_eq (finitePunctureDomain (P n)) hc
      (show x ∈ finitePunctureDomain (P n) from hxP n) hxc
    simp_rw [he]
    exact hρ.atTop_div_const (p.density_pos hc hxc)
  exact ENNReal.tendsto_ofReal_atTop.comp ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp hr)

variable [MeasurableSpace M] [BorelSpace M]

/-- An actual finite-puncture area bound forces nullity on the limiting
closed complement. Countably many punctures are discarded using their
proved zero intrinsic area. This is the geometric Fatou step used by the
positive-area dynamical argument. -/
theorem measure_zero_of_finite_model_area_bounds (p : DiscCover M)
    (P : ℕ → Finset M) (hP : Monotone P) {B : Set M}
    (hB : MeasurableSet B) (hBP : B ⊆ closure (⋃ n, (P n : Set M)))
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ n, p.domainArea (finitePunctureDomain (P n)) B ≤ C) :
    p.hyperbolicArea B = 0 := by
  let : NullSingletonClass p.hyperbolicArea := p.hyperbolicArea_noAtoms
  have hnull : p.hyperbolicArea (⋃ n, (P n : Set M)) = 0 :=
    (countable_iUnion (fun n => (P n).finite_toSet.countable)).measure_zero _
  have hae : ∀ᵐ x ∂p.hyperbolicArea, x ∉ ⋃ n, (P n : Set M) := by
    simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hnull
  apply AreaDeficit.measure_zero_of_density_blowup (w := fun n x =>
    ENNReal.ofReal ((p.domainDensityRatio (finitePunctureDomain (P n)) x)^2)) hC
  · intro n
    exact (((p.domainDensityRatio_measurable _).pow_const 2).ennreal_ofReal).aemeasurable
  · filter_upwards [ae_restrict_of_ae hae,ae_restrict_mem hB] with x hx hxB
    exact p.domainAreaWeight_tendsto_top P hP
      (fun n hxn => hx (mem_iUnion.mpr ⟨n,hxn⟩)) (hBP hxB)
  · intro n
    simpa only [domainArea,withDensity_apply _ hB] using hbound n

end AreaDeficit.Surfaces.DiscCover
