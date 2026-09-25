/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DomainArea
import BoundedWanderingDomains.Surfaces.HyperbolicAreaFinite
import BoundedWanderingDomains.Surfaces.CompactFiniteRemoval

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

end AreaDeficit.Surfaces.DiscCover
