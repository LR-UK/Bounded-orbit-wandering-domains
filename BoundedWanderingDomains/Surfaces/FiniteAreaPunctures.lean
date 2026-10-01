module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.FiniteModelArea
public import BoundedWanderingDomains.Surfaces.DiscComparisonInfinity

@[expose] public section

open Set Function Filter MeasureTheory
open scoped Manifold Topology ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]
  [LocallyCompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Inserting finitely many punctures preserves finiteness of the area
of any measurable set, even if that set is not relatively compact. -/
theorem finitePunctureDomain_area_finite_of_hyperbolicArea_finite
    (p : DiscCover M) (P : Finset M)
    {A : Set M} (hA : MeasurableSet A) (hp : p.hyperbolicArea A < ⊤) :
    p.domainArea (finitePunctureDomain P) A < ⊤ := by
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
  have hout : p.domainArea U (A \ C) ≤
      ENNReal.ofReal 4 * p.hyperbolicArea (A \ C) := by
    rw [domainArea, withDensity_apply _ (hA.diff hC.measurableSet)]
    calc
      (∫⁻ x in (A \ C), ENNReal.ofReal ((p.domainDensityRatio U x)^2)
          ∂p.hyperbolicArea) ≤
          ∫⁻ _x in (A \ C), ENNReal.ofReal 4 ∂p.hyperbolicArea := by
            apply setLIntegral_mono' (hA.diff hC.measurableSet)
            intro x hx
            apply ENNReal.ofReal_le_ofReal
            have hn := p.domainDensityRatio_nonneg U x
            nlinarith [hratio x hx.2]
      _ = ENNReal.ofReal 4 * p.hyperbolicArea (A \ C) := by
        rw [setLIntegral_const]
  have houtfin : p.domainArea U (A \ C) < ⊤ :=
    lt_of_le_of_lt hout (ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
      (lt_of_le_of_lt (measure_mono sdiff_subset) hp))
  have hinfin : p.domainArea U C < ⊤ :=
    p.finitePunctureDomain_area_compact_finite P hC
  apply lt_of_le_of_lt (measure_mono (show A ⊆ C ∪ (A \ C) by intro x hx; by_cases hc : x ∈ C; exact Or.inl hc; exact Or.inr ⟨hx, hc⟩))
  exact lt_of_le_of_lt (measure_union_le C (A \ C))
    (ENNReal.add_lt_top.mpr ⟨hinfin, houtfin⟩)

end AreaDeficit.Surfaces.DiscCover
