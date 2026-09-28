/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.AnchorComplementModels
import BoundedWanderingDomains.Surfaces.PositiveAreaAdvanceReduction
import BoundedWanderingDomains.Surfaces.PositiveAreaBridge
import BoundedWanderingDomains.Surfaces.GlobalFinitePunctureArea
import BoundedWanderingDomains.Surfaces.CompactFinitePunctureArea
import BoundedWanderingDomains.Surfaces.SphereGlobalPointInsertion
import BoundedWanderingDomains.Surfaces.CompactificationInsertionRiesz

/-! # Compact anchor-complement area reduction -/

open Set Function MeasureTheory TopologicalSpace
open scoped Manifold Topology ENNReal

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [SecondCountableTopology X]
  [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [DecidableEq X]

omit [LocallyCompactSpace X] [DecidableEq X] in
/-- A fixed finite anchor complement in a compact surface has finite total
hyperbolic area. -/
theorem anchorComplement_hyperbolicArea_lt_top [CompactSpace X]
    (E : Finset X)
    (p : AreaDeficit.Surfaces.DiscCover
      (AreaDeficit.Surfaces.anchorComplement E)) :
    p.hyperbolicArea Set.univ < ⊤ := by
  exact AreaDeficit.Surfaces.DiscCover.hyperbolicArea_compl_finset_lt_top
    E (AreaDeficit.Surfaces.anchorComplement E) (fun _ => Iff.rfl)
      ⟨p.projection AreaDeficit.Surfaces.discZero⟩ p

omit [DecidableEq X] in
/-- Every further finite stage inside the anchor complement also has finite
total domain area. -/
theorem anchorComplement_finiteStage_area_lt_top [CompactSpace X]
    (E F : Finset X)
    (p : AreaDeficit.Surfaces.DiscCover
      (AreaDeficit.Surfaces.anchorComplement E)) :
    p.domainArea
      (AreaDeficit.Surfaces.finitePunctureDomain
        (AreaDeficit.Surfaces.finiteStageOnAnchorComplement E F))
      Set.univ < ⊤ := by
  let : LocallyCompactSpace
      (AreaDeficit.Surfaces.anchorComplement E) :=
    (AreaDeficit.Surfaces.anchorComplement E).isOpen.locallyCompactSpace
  exact p.finitePunctureDomain_area_univ_finite_of_hyperbolicArea_univ_finite
    (AreaDeficit.Surfaces.finiteStageOnAnchorComplement E F)
    (anchorComplement_hyperbolicArea_lt_top E p)

/-- For a compact surface, the full anchor-complement package now follows
from just the uniform one-point insertion estimate.  The finite-total-area
half is supplied by the cusp calculation above, while finite insertion is
obtained by telescoping the one-point bound. -/
theorem anchorComplement_globalFinitePunctureAreaPackage_of_pointInsertion
    [CompactSpace X] (E : Finset X)
    (p : AreaDeficit.Surfaces.DiscCover
      (AreaDeficit.Surfaces.anchorComplement E))
    (q : ℕ) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hpoint : p.UniformGlobalPointInsertionBound C) :
    p.GlobalFinitePunctureAreaPackage q := by
  let : LocallyCompactSpace
      (AreaDeficit.Surfaces.anchorComplement E) :=
    (AreaDeficit.Surfaces.anchorComplement E).isOpen.locallyCompactSpace
  exact p.globalFinitePunctureAreaPackage_of_pointInsertion q
    (anchorComplement_hyperbolicArea_lt_top E p) hC hpoint

/-- The uniform compactification insertion estimate supplies the complete
finite-puncture area package on every connected finite anchor complement. -/
theorem anchorComplement_globalFinitePunctureAreaPackage
    [CompactSpace X] [ConnectedSpace X] [Infinite X] (E : Finset X)
    (p : AreaDeficit.Surfaces.DiscCover
      (AreaDeficit.Surfaces.anchorComplement E)) (q : ℕ) :
    p.GlobalFinitePunctureAreaPackage q := by
  let O := AreaDeficit.Surfaces.anchorComplement E
  let : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  let : ConnectedSpace O := Subtype.connectedSpace
    (RiemannDynamics.isConnected_compl_finset E)
  let : Infinite O := Set.Infinite.to_subtype E.finite_toSet.infinite_compl
  exact anchorComplement_globalFinitePunctureAreaPackage_of_pointInsertion
    E p q ENNReal.ofReal_ne_top
    (AreaDeficit.Surfaces.FinitePunctureDiscs.DiscCover.compactification_uniformGlobalPointInsertionBound
      E O (fun _ => Iff.rfl) ⟨p.projection AreaDeficit.Surfaces.discZero⟩ p)

/-- On a compact surface biholomorphic to the sphere, three distinct anchors
give the complete finite-puncture area package, with the sharp one-point cost
`2π`.  This is the compact sphere branch of the global area reduction. -/
theorem anchorComplement_globalFinitePunctureAreaPackage_of_diffeomorph_sphere
    [CompactSpace X] [IsManifold 𝓘(ℂ) ⊤ X]
    {a b c : X} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (e : X ≃ₘ^⊤⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ̂)
    (p : AreaDeficit.Surfaces.DiscCover
      (AreaDeficit.Surfaces.anchorComplement ({a, b, c} : Finset X)))
    (q : ℕ) :
    p.GlobalFinitePunctureAreaPackage q := by
  apply anchorComplement_globalFinitePunctureAreaPackage_of_pointInsertion
      ({a, b, c} : Finset X) p q
      (ENNReal.ofReal_ne_top : ENNReal.ofReal (2 * Real.pi) ≠ ⊤)
  exact p.uniformGlobalPointInsertionBound_of_diffeomorph_sphere
    hab hac hbc e _
      (by intro x; simp [AreaDeficit.Surfaces.anchorComplement])

/-- On a compact surface with fixed hyperbolising anchors, the last global
point-removal input is exactly the total-area increase caused by inserting
one further puncture.  Finiteness of every stage is discharged internally. -/
theorem anchorComplement_pointInsertion_iff_totalArea_increment
    [CompactSpace X] (E : Finset X)
    (p : AreaDeficit.Surfaces.DiscCover
      (AreaDeficit.Surfaces.anchorComplement E)) {C : ℝ≥0∞} :
    p.UniformGlobalPointInsertionBound C ↔
      ∀ (P : Finset (AreaDeficit.Surfaces.anchorComplement E))
        (a : AreaDeficit.Surfaces.anchorComplement E),
        p.domainArea
            (AreaDeficit.Surfaces.finitePunctureDomain (insert a P)) Set.univ ≤
          p.domainArea
            (AreaDeficit.Surfaces.finitePunctureDomain P) Set.univ + C := by
  let : LocallyCompactSpace
      (AreaDeficit.Surfaces.anchorComplement E) :=
    (AreaDeficit.Surfaces.anchorComplement E).isOpen.locallyCompactSpace
  apply p.uniformGlobalPointInsertionBound_iff_totalArea_increment
  intro P
  exact (p.finitePunctureDomain_area_univ_finite_of_hyperbolicArea_univ_finite
    P (anchorComplement_hyperbolicArea_lt_top E p)).ne

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
  let : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
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
  let : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
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
