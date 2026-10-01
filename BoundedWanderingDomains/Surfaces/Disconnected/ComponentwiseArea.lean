module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseCover
public import BoundedWanderingDomains.Surfaces.DomainArea

@[expose] public section

/-! # Intrinsic area on a disjoint union of hyperbolic surfaces

The measure is the sum of the intrinsic measures on the ambient components.
There is no choice of a preferred ambient component and no assumption that a
local map preserves any of them.
-/

open Set Function MeasureTheory TopologicalSpace
open scoped Manifold ENNReal

namespace AreaDeficit.Surfaces.ComponentwiseDiscCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

noncomputable def domainArea (p : ComponentwiseDiscCover X) (U : Opens X) : Measure X :=
  Measure.sum (fun c : ConnectedComponents X =>
    Measure.map (Subtype.val : ambientComponent c → X)
      ((p.cover c).domainArea (componentPart c U)))

noncomputable def hyperbolicArea (p : ComponentwiseDiscCover X) : Measure X :=
  p.domainArea ⊤

theorem domainArea_apply (p : ComponentwiseDiscCover X) (U : Opens X)
    {A : Set X} (hA : MeasurableSet A) :
    p.domainArea U A = ∑' c : ConnectedComponents X,
      (p.cover c).domainArea (componentPart c U) (Subtype.val ⁻¹' A) := by
  rw [domainArea, Measure.sum_apply _ hA]
  apply tsum_congr
  intro c
  exact Measure.map_apply continuous_subtype_val.measurable hA

theorem domainArea_apply_of_subset_component (p : ComponentwiseDiscCover X)
    (U : Opens X) (c : ConnectedComponents X) {A : Set X}
    (hA : MeasurableSet A) (hAc : A ⊆ ambientComponent c) :
    p.domainArea U A =
      (p.cover c).domainArea (componentPart c U) (Subtype.val ⁻¹' A) := by
  rw [p.domainArea_apply U hA]
  apply tsum_eq_single c
  intro d hdc
  have hempty : (Subtype.val ⁻¹' A : Set (ambientComponent d)) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hdc (x.property.symm.trans (hAc hx))
  rw [hempty, measure_empty]

theorem hyperbolicArea_apply_of_subset_component (p : ComponentwiseDiscCover X)
    (c : ConnectedComponents X) {A : Set X} (hA : MeasurableSet A)
    (hAc : A ⊆ ambientComponent c) :
    p.hyperbolicArea A = (p.cover c).hyperbolicArea (Subtype.val ⁻¹' A) := by
  rw [hyperbolicArea, p.domainArea_apply_of_subset_component ⊤ c hA hAc,
    componentPart_top, DiscCover.domainArea_top]

theorem domainArea_independent (p q : ComponentwiseDiscCover X) (U : Opens X) :
    p.domainArea U = q.domainArea U := by
  apply Measure.ext
  intro A hA
  rw [p.domainArea_apply U hA, q.domainArea_apply U hA]
  apply tsum_congr
  intro c
  rw [(p.cover c).domainArea_independent (q.cover c)]

theorem domainArea_mono_on (p : ComponentwiseDiscCover X)
    {U V : Opens X} (hVU : V ≤ U) {A : Set X} (hA : MeasurableSet A)
    (hAV : A ⊆ V) : p.domainArea U A ≤ p.domainArea V A := by
  rw [p.domainArea_apply U hA, p.domainArea_apply V hA]
  apply ENNReal.tsum_le_tsum
  intro c
  exact (p.cover c).domainArea_mono_on (componentPart_mono c hVU)
    (hA.preimage continuous_subtype_val.measurable) (fun _ hx => hAV hx)

end AreaDeficit.Surfaces.ComponentwiseDiscCover
