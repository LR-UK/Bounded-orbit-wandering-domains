module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseArea
public import BoundedWanderingDomains.Surfaces.FiniteModelArea

@[expose] public section

/-! # Finite area of puncture models on compact sets in disconnected surfaces -/

open Set Function MeasureTheory TopologicalSpace Topology
open scoped Manifold ENNReal

namespace AreaDeficit.Surfaces.ComponentwiseDiscCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [SecondCountableTopology X]
  [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

omit [LocallyCompactSpace X] in
theorem domainArea_apply_finite_component_cover (p : ComponentwiseDiscCover X)
    (U : Opens X) (I : Finset (ConnectedComponents X)) {A : Set X}
    (hA : MeasurableSet A) (hAI : A ⊆ ⋃ c ∈ I, (ambientComponent c : Set X)) :
    p.domainArea U A = ∑ c ∈ I,
      (p.cover c).domainArea (componentPart c U) (Subtype.val ⁻¹' A) := by
  classical
  rw [p.domainArea_apply U hA]
  apply tsum_eq_sum
  intro c hc
  have hempty : (Subtype.val ⁻¹' A : Set (ambientComponent c)) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp (hAI hx)
    have hcd : c = d := x.property.symm.trans hxd
    exact hc (hcd.symm ▸ hd)
  rw [hempty, measure_empty]

theorem finitePunctureDomain_area_compact_finite (p : ComponentwiseDiscCover X)
    (P : Finset X) {K : Set X} (hK : IsCompact K) :
    p.domainArea (finitePunctureDomain P) K < ⊤ := by
  obtain ⟨I, hI⟩ := exists_finite_component_cover hK
  rw [p.domainArea_apply_finite_component_cover _ I hK.measurableSet hI]
  apply ENNReal.sum_lt_top.mpr
  intro c hc
  rw [componentPart_finitePunctureDomain]
  let : LocallyCompactSpace (ambientComponent c) :=
    (ambientComponent c).isOpen.locallyCompactSpace
  exact (p.cover c).finitePunctureDomain_area_compact_finite (componentPunctures c P)
    ((isClosed_ambientComponent c).isClosedEmbedding_subtypeVal.isCompact_preimage hK)

theorem finitePunctureDomain_area_subset_compact_finite (p : ComponentwiseDiscCover X)
    (P : Finset X) {K A : Set X} (hK : IsCompact K) (hAK : A ⊆ K) :
    p.domainArea (finitePunctureDomain P) A ≠ ⊤ :=
  ne_top_of_le_ne_top (p.finitePunctureDomain_area_compact_finite P hK).ne (measure_mono hAK)

end AreaDeficit.Surfaces.ComponentwiseDiscCover
