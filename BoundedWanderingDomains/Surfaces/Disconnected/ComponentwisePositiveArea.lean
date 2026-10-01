module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseArea
public import BoundedWanderingDomains.Surfaces.PositiveAreaBridge

@[expose] public section

/-! # Chart area and exceptional sets on disconnected hyperbolic manifolds -/

open Set MeasureTheory
open AreaDeficit.Surfaces
open scoped Manifold ENNReal

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

omit [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
theorem HasPositiveChartArea.exists_ambient_component {A : Set X}
    (hA : HasPositiveChartArea A) :
    ∃ c : ConnectedComponents X, HasPositiveChartArea (A ∩ ambientComponent c) := by
  classical
  let : Countable (ConnectedComponents X) := countable_ambient_components
  by_contra hno
  obtain ⟨x, hx⟩ := hA
  let chart := chartAt ℂ x
  have hz : ∀ c : ConnectedComponents X,
      volume (chart '' ((A ∩ ambientComponent c) ∩ chart.source)) = 0 := by
    intro c
    apply le_antisymm _ bot_le
    apply le_of_not_gt
    intro hpos
    exact hno ⟨c, x, hpos⟩
  have he : chart '' (A ∩ chart.source) =
      ⋃ c : ConnectedComponents X, chart '' ((A ∩ ambientComponent c) ∩ chart.source) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mem_iUnion.mpr ⟨ConnectedComponents.mk y, y, ⟨⟨hy.1, rfl⟩, hy.2⟩, rfl⟩
    · intro hz
      obtain ⟨c, y, hy, rfl⟩ := mem_iUnion.mp hz
      exact ⟨y, ⟨hy.1.1, hy.2⟩, rfl⟩
  have hzero : volume (chart '' (A ∩ chart.source)) = 0 := by
    rw [he]
    exact measure_iUnion_null hz
  exact (ne_of_gt hx) hzero

theorem HasPositiveChartArea.componentwise_hyperbolicArea_pos {A : Set X}
    (hA : HasPositiveChartArea A) (hm : MeasurableSet A)
    (p : ComponentwiseDiscCover X) : 0 < p.hyperbolicArea A := by
  obtain ⟨c, hc⟩ := hA.exists_ambient_component
  have hAc : MeasurableSet (A ∩ ambientComponent c) :=
    hm.inter (ambientComponent c).isOpen.measurableSet
  have hpos := hc.hyperbolicArea_pos_openSubtype hAc (ambientComponent c)
    inter_subset_right (p.cover c)
  rw [← p.hyperbolicArea_apply_of_subset_component c hAc inter_subset_right] at hpos
  exact hpos.trans_le (measure_mono inter_subset_left)

theorem componentwise_hyperbolicArea_countable_zero
    (p : ComponentwiseDiscCover X) {S : Set X} (hS : S.Countable) :
    p.hyperbolicArea S = 0 := by
  rw [ComponentwiseDiscCover.hyperbolicArea, p.domainArea_apply _ hS.measurableSet]
  apply ENNReal.tsum_eq_zero.mpr
  intro c
  rw [componentPart_top, DiscCover.domainArea_top]
  exact hyperbolicArea_countable_zero (p.cover c)
    (hS.preimage Subtype.val_injective)

theorem componentwise_hyperbolicArea_diff_countable
    (p : ComponentwiseDiscCover X) (A : Set X) {S : Set X} (hS : S.Countable) :
    p.hyperbolicArea (A \ S) = p.hyperbolicArea A :=
  measure_sdiff_null (componentwise_hyperbolicArea_countable_zero p hS)

end SurfaceDynamics
