/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.FiniteModelCancellation
import BoundedWanderingDomains.Surfaces.PositiveAreaContradiction

/-! # Reduction of the positive-area theorem to one-step area advance -/

open Set MeasureTheory
open scoped Manifold ENNReal

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [SecondCountableTopology X]
  [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] [DecidableEq X]

/-- Measure-theoretic version of finite-model cancellation. -/
theorem false_of_positive_hyperbolicArea_area_advances
    (p : AreaDeficit.Surfaces.DiscCover X)
    (P : ℕ → Finset X) (hP : Monotone P) {A : Set X}
    (hA : MeasurableSet A) (hApos : 0 < p.hyperbolicArea A)
    (hAP : A ⊆ closure (⋃ n, (P n : Set X)))
    (q : ℕ) {L : Set X} (hL : IsCompact L)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hadvance : ∀ n, ∃ (E : Finset X) (f : X → X) (W : Set X),
      E.card ≤ q ∧ A ⊆ W ∧ W ⊆ L ∧ MeasurableSet (f '' W) ∧
      f '' W ⊆ W \ A ∧
      p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain (P n)) W ≤
        p.domainArea
          (AreaDeficit.Surfaces.finitePunctureDomain (P n ∪ E)) (f '' W) + C) :
    False := by
  obtain ⟨H, hH, hcancel⟩ :=
    p.finite_model_cancellation_of_area_advance q hL hC
  apply false_of_positive_hyperbolicArea_finite_model_bounds
    p P hP hA hApos hAP hH
  intro n
  obtain ⟨E, f, W, hEq, hAW, hWL, hfW, himage, hstep⟩ := hadvance n
  exact hcancel (P n) E hEq f A W hA hAW hWL hfW himage hstep

/-- All topological, exceptional-set, finite-area, puncture-cost, and Fatou
steps are discharged here.  To rule out a positive-area wandering set it is
enough to supply the uniform one-step area-advance configuration in each
finite puncture model. -/
theorem false_of_positive_area_area_advances
    (p : AreaDeficit.Surfaces.DiscCover X)
    (P : ℕ → Finset X) (hP : Monotone P) {A : Set X}
    (hA : MeasurableSet A) (hApos : HasPositiveChartArea A)
    (hAP : A ⊆ closure (⋃ n, (P n : Set X)))
    (q : ℕ) {L : Set X} (hL : IsCompact L)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hadvance : ∀ n, ∃ (E : Finset X) (f : X → X) (W : Set X),
      E.card ≤ q ∧ A ⊆ W ∧ W ⊆ L ∧ MeasurableSet (f '' W) ∧
      f '' W ⊆ W \ A ∧
      p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain (P n)) W ≤
        p.domainArea
          (AreaDeficit.Surfaces.finitePunctureDomain (P n ∪ E)) (f '' W) + C) :
    False := by
  exact false_of_positive_hyperbolicArea_area_advances p P hP hA
    (hApos.hyperbolicArea_pos hA p) hAP q hL hC hadvance

/-- Intrinsic global finite-area version of the cancellation reduction.
Compact containment is replaced by the exact two facts it supplied in the
local proof: finiteness of the old model on the wandering union and a
uniform cost for the newly inserted finite exceptional set. -/
theorem false_of_positive_hyperbolicArea_global_area_advances
    (p : AreaDeficit.Surfaces.DiscCover X)
    (P : ℕ → Finset X) (hP : Monotone P) {A : Set X}
    (hA : MeasurableSet A) (hApos : 0 < p.hyperbolicArea A)
    (hAP : A ⊆ closure (⋃ n, (P n : Set X)))
    {C D : ℝ≥0∞} (hC : C ≠ ⊤) (hD : D ≠ ⊤)
    (hadvance : ∀ n, ∃ (E : Finset X) (f : X → X) (W : Set X),
      A ⊆ W ∧ MeasurableSet (f '' W) ∧ f '' W ⊆ W \ A ∧
      p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain (P n)) W ≠ ⊤ ∧
      p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain (P n)) W ≤
        p.domainArea
          (AreaDeficit.Surfaces.finitePunctureDomain (P n ∪ E)) (f '' W) + C ∧
      p.domainArea
          (AreaDeficit.Surfaces.finitePunctureDomain (P n ∪ E)) (f '' W) ≤
        p.domainArea
          (AreaDeficit.Surfaces.finitePunctureDomain (P n)) (f '' W) + D) :
    False := by
  apply false_of_positive_hyperbolicArea_finite_model_bounds
    p P hP hA hApos hAP (C := D + C)
      (ENNReal.add_ne_top.mpr ⟨hD, hC⟩)
  intro n
  obtain ⟨E, f, W, hAW, hfW, himage, hfinite, hstep, hcost⟩ := hadvance n
  exact AreaDeficit.finite_area_cancellation_le hA hAW hfinite himage hstep hcost

/-- Global finite-area version of the cancellation reduction.  Compact
containment is replaced by the exact two facts it supplied in the local
proof: finiteness of the old model on the wandering union and a uniform
cost for the newly inserted finite exceptional set. -/
theorem false_of_positive_area_global_area_advances
    (p : AreaDeficit.Surfaces.DiscCover X)
    (P : ℕ → Finset X) (hP : Monotone P) {A : Set X}
    (hA : MeasurableSet A) (hApos : HasPositiveChartArea A)
    (hAP : A ⊆ closure (⋃ n, (P n : Set X)))
    {C D : ℝ≥0∞} (hC : C ≠ ⊤) (hD : D ≠ ⊤)
    (hadvance : ∀ n, ∃ (E : Finset X) (f : X → X) (W : Set X),
      A ⊆ W ∧ MeasurableSet (f '' W) ∧ f '' W ⊆ W \ A ∧
      p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain (P n)) W ≠ ⊤ ∧
      p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain (P n)) W ≤
        p.domainArea
          (AreaDeficit.Surfaces.finitePunctureDomain (P n ∪ E)) (f '' W) + C ∧
      p.domainArea
          (AreaDeficit.Surfaces.finitePunctureDomain (P n ∪ E)) (f '' W) ≤
        p.domainArea
          (AreaDeficit.Surfaces.finitePunctureDomain (P n)) (f '' W) + D) :
    False := by
  exact false_of_positive_hyperbolicArea_global_area_advances
    p P hP hA (hApos.hyperbolicArea_pos hA p) hAP hC hD hadvance

end SurfaceDynamics

#print axioms SurfaceDynamics.false_of_positive_area_area_advances
#print axioms SurfaceDynamics.false_of_positive_hyperbolicArea_area_advances
#print axioms SurfaceDynamics.false_of_positive_area_global_area_advances
#print axioms SurfaceDynamics.false_of_positive_hyperbolicArea_global_area_advances
