/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DomainArea
import BoundedWanderingDomains.Surfaces.HyperbolicAreaFinite
import BoundedWanderingDomains.Surfaces.CompactFiniteRemoval
import BoundedWanderingDomains.Surfaces.DiscComparisonInfinity

/-! # Finite area of finite-puncture models on compact measured sets

The entire surface may have infinite area. Local finiteness and the
checked compact puncture budget justify finite-model cancellation.
-/
open Set Function Filter MeasureTheory
open scoped Manifold Topology ENNReal
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]
  [LocallyCompactSpace M] [MeasurableSpace M] [BorelSpace M]

theorem finitePunctureDomain_area_compact_finite (p : DiscCover M) (P : Finset M)
    {L : Set M} (hL : IsCompact L) :
    p.domainArea (finitePunctureDomain P) L < ⊤ := by
  obtain ⟨B,hB,hbound⟩ := p.compact_finite_removal_gain P hL
  have he : finiteRemovalDomain (⊤ : TopologicalSpace.Opens M) P =
      finitePunctureDomain P := by
    ext x
    change (x ∈ (Set.univ : Set M) ∧ x ∉ (P : Set M)) ↔ x ∉ (P : Set M)
    simp
  have hg : p.domainAreaGain ⊤ (finitePunctureDomain P) L ≤ B := by
    simpa only [he] using hbound ⊤
  calc
    p.domainArea (finitePunctureDomain P) L ≤
        p.domainArea ⊤ L + p.domainAreaGain ⊤ (finitePunctureDomain P) L :=
      p.domainArea_le_add_gain ⊤ _ hL.measurableSet
    _ ≤ p.hyperbolicArea L + B := by rw [p.domainArea_top]; exact add_le_add_right hg _
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨p.hyperbolicArea_compact_finite hL,lt_top_iff_ne_top.mpr hB⟩

theorem finitePunctureDomain_area_subset_compact_finite (p : DiscCover M) (P : Finset M)
    {L E : Set M} (hL : IsCompact L) (hEL : E ⊆ L) :
    p.domainArea (finitePunctureDomain P) E ≠ ⊤ :=
  ne_top_of_le_ne_top (p.finitePunctureDomain_area_compact_finite P hL).ne (measure_mono hEL)

/-- If the ambient hyperbolic surface has finite total area, all finite
puncture models also have finite total area. -/
theorem finitePunctureDomain_area_univ_finite_of_hyperbolicArea_univ_finite
    (p : DiscCover M) (P : Finset M)
    (hp : p.hyperbolicArea Set.univ < ⊤) :
    p.domainArea (finitePunctureDomain P) Set.univ < ⊤ := by
  classical
  let U := finitePunctureDomain P
  obtain ⟨C, hC, hbound⟩ := p.domainDensity_ratio_le_outside_compact
    P.finite_toSet.isCompact (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hratio : ∀ x : M, x ∉ C → p.domainDensityRatio U x ≤ 2 := by
    intro x hxC
    by_cases hxU : x ∈ U
    · let c := chartAt ℂ x
      have hc := (mdifferentiable_chart (I := 𝓘(ℂ)) x).1
      have hxc : x ∈ c.source := mem_chart_source ℂ x
      have hle : U ≤ (⊤ : TopologicalSpace.Opens M) := fun _ _ => mem_univ _
      have houtside : ∀ y ∈ (⊤ : TopologicalSpace.Opens M),
          y ∉ (↑P : Set M) → y ∈ U := by
        intro y _ hy
        exact hy
      have h := hbound ⊤ U hle houtside c hc
        (⟨x, hxU⟩ : U) hxC hxc
      rw [p.domainDensityRatio_eq U hc hxU hxc]
      norm_num at h ⊢
      have htop : p.domainDensity ⊤ c ⟨x, mem_univ x⟩ =
          p.density c x := p.domainDensity_top hc hxc
      rw [htop] at h
      simpa only [c] using h
    · simp [domainDensityRatio, hxU]
  have hout : p.domainArea U Cᶜ ≤
      ENNReal.ofReal 4 * p.hyperbolicArea Cᶜ := by
    rw [domainArea, withDensity_apply _ hC.isClosed.measurableSet.compl]
    calc
      (∫⁻ x in Cᶜ, ENNReal.ofReal ((p.domainDensityRatio U x)^2)
          ∂p.hyperbolicArea) ≤
          ∫⁻ _x in Cᶜ, ENNReal.ofReal 4 ∂p.hyperbolicArea := by
            apply setLIntegral_mono' hC.isClosed.measurableSet.compl
            intro x hx
            apply ENNReal.ofReal_le_ofReal
            have hn := p.domainDensityRatio_nonneg U x
            nlinarith [hratio x hx]
      _ = ENNReal.ofReal 4 * p.hyperbolicArea Cᶜ := by
        rw [setLIntegral_const]
  have houtfin : p.domainArea U Cᶜ < ⊤ :=
    lt_of_le_of_lt hout (ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
      (lt_of_le_of_lt (measure_mono (subset_univ Cᶜ)) hp))
  have hinfin : p.domainArea U C < ⊤ :=
    p.finitePunctureDomain_area_compact_finite P hC
  apply lt_of_le_of_lt (measure_mono (show (Set.univ : Set M) ⊆ C ∪ Cᶜ by simp))
  exact lt_of_le_of_lt (measure_union_le C Cᶜ)
    (ENNReal.add_lt_top.mpr ⟨hinfin, houtfin⟩)

end AreaDeficit.Surfaces.DiscCover

#print axioms AreaDeficit.Surfaces.DiscCover.finitePunctureDomain_area_univ_finite_of_hyperbolicArea_univ_finite
