/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.AnchorComplementModels
import BoundedWanderingDomains.Surfaces.PositiveAreaAdvanceReduction
import BoundedWanderingDomains.Surfaces.PositiveAreaBridge
import BoundedWanderingDomains.Surfaces.GlobalFinitePunctureArea

/-! # Compact anchor-complement area reduction -/

open Set Function MeasureTheory TopologicalSpace
open scoped Manifold Topology ENNReal

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [SecondCountableTopology X]
  [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [DecidableEq X]

/-- Transfer the global finite-area contradiction to a fixed complement of
compact-surface anchors.  Ambient finite stages are restricted to the open
subsurface; their density at the measured set is preserved. -/
theorem false_of_anchorComplement_global_area_advances
    (E : Finset X)
    (p : AreaDeficit.Surfaces.DiscCover
      (AreaDeficit.Surfaces.anchorComplement E))
    (P : ℕ → Finset X) (hP : Monotone P)
    {A : Set X} (hA : MeasurableSet A) (hApos : HasPositiveChartArea A)
    (hAE : Disjoint A (↑E : Set X))
    (hAP : A ⊆ closure (⋃ n, (P n : Set X)))
    {C D : ℝ≥0∞} (hC : C ≠ ⊤) (hD : D ≠ ⊤)
    (hadvance :
      let O := AreaDeficit.Surfaces.anchorComplement E
      let Q : ℕ → Finset O := fun n =>
        AreaDeficit.Surfaces.finiteStageOnAnchorComplement E (P n)
      let AO : Set O := (Subtype.val : O → X) ⁻¹' A
      ∀ n, ∃ (R : Finset O) (f : O → O) (W : Set O),
        AO ⊆ W ∧ MeasurableSet (f '' W) ∧ f '' W ⊆ W \ AO ∧
        p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain (Q n)) W ≠ ⊤ ∧
        p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain (Q n)) W ≤
          p.domainArea
            (AreaDeficit.Surfaces.finitePunctureDomain (Q n ∪ R)) (f '' W) + C ∧
        p.domainArea
            (AreaDeficit.Surfaces.finitePunctureDomain (Q n ∪ R)) (f '' W) ≤
          p.domainArea
            (AreaDeficit.Surfaces.finitePunctureDomain (Q n)) (f '' W) + D) :
    False := by
  let O := AreaDeficit.Surfaces.anchorComplement E
  letI : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  let Q : ℕ → Finset O := fun n =>
    AreaDeficit.Surfaces.finiteStageOnAnchorComplement E (P n)
  let AO : Set O := (Subtype.val : O → X) ⁻¹' A
  have hAOsub : A ⊆ O := by
    intro x hxA hxE
    exact Set.disjoint_left.mp hAE hxA hxE
  have hAOmeas : MeasurableSet AO :=
    hA.preimage continuous_subtype_val.measurable
  have hAOarea : 0 < p.hyperbolicArea AO :=
    hApos.hyperbolicArea_pos_openSubtype hA O hAOsub p
  have hQmono : Monotone Q :=
    AreaDeficit.Surfaces.finiteStageOnAnchorComplement_monotone E hP
  have hAOQ : AO ⊆ closure (⋃ n, (Q n : Set O)) := by
    intro x hxA
    exact AreaDeficit.Surfaces.mem_closure_iUnion_finiteStageOnAnchorComplement
      E P x (hAP hxA)
  exact false_of_positive_hyperbolicArea_global_area_advances
    p Q hQmono hAOmeas hAOarea hAOQ hC hD hadvance

/-- Package form of the anchor-complement reduction.  After finite-type
global area and puncture cost are supplied, only the uniform one-step area
advance remains. -/
theorem false_of_anchorComplement_global_package
    (E : Finset X)
    (p : AreaDeficit.Surfaces.DiscCover
      (AreaDeficit.Surfaces.anchorComplement E))
    (q : ℕ) (hp : p.GlobalFinitePunctureAreaPackage q)
    (P : ℕ → Finset X) (hP : Monotone P)
    {A : Set X} (hA : MeasurableSet A) (hApos : HasPositiveChartArea A)
    (hAE : Disjoint A (↑E : Set X))
    (hAP : A ⊆ closure (⋃ n, (P n : Set X)))
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hadvance :
      let O := AreaDeficit.Surfaces.anchorComplement E
      let Q : ℕ → Finset O := fun n =>
        AreaDeficit.Surfaces.finiteStageOnAnchorComplement E (P n)
      let AO : Set O := (Subtype.val : O → X) ⁻¹' A
      ∀ n, ∃ (R : Finset O) (f : O → O) (W : Set O),
        R.card ≤ q ∧ AO ⊆ W ∧ MeasurableSet (f '' W) ∧
        f '' W ⊆ W \ AO ∧
        p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain (Q n)) W ≤
          p.domainArea
            (AreaDeficit.Surfaces.finitePunctureDomain (Q n ∪ R)) (f '' W) + C) :
    False := by
  let O := AreaDeficit.Surfaces.anchorComplement E
  letI : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  let Q : ℕ → Finset O := fun n =>
    AreaDeficit.Surfaces.finiteStageOnAnchorComplement E (P n)
  let AO : Set O := (Subtype.val : O → X) ⁻¹' A
  have hAOsub : A ⊆ O := by
    intro x hxA hxE
    exact Set.disjoint_left.mp hAE hxA hxE
  have hAOmeas : MeasurableSet AO :=
    hA.preimage continuous_subtype_val.measurable
  have hAOarea : 0 < p.hyperbolicArea AO :=
    hApos.hyperbolicArea_pos_openSubtype hA O hAOsub p
  have hQmono : Monotone Q :=
    AreaDeficit.Surfaces.finiteStageOnAnchorComplement_monotone E hP
  have hAOQ : AO ⊆ closure (⋃ n, (Q n : Set O)) := by
    intro x hxA
    exact AreaDeficit.Surfaces.mem_closure_iUnion_finiteStageOnAnchorComplement
      E P x (hAP hxA)
  exact false_of_positive_hyperbolicArea_global_package
    p q hp Q hQmono hAOmeas hAOarea hAOQ hC hadvance

end SurfaceDynamics

#print axioms SurfaceDynamics.false_of_anchorComplement_global_area_advances
#print axioms SurfaceDynamics.false_of_anchorComplement_global_package
