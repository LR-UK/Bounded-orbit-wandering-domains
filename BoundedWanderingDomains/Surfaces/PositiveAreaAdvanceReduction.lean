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
  obtain ⟨H, hH, hcancel⟩ :=
    p.finite_model_cancellation_of_area_advance q hL hC
  apply false_of_positive_area_finite_model_bounds p P hP hA hApos hAP hH
  intro n
  obtain ⟨E, f, W, hEq, hAW, hWL, hfW, himage, hstep⟩ := hadvance n
  exact hcancel (P n) E hEq f A W hA hAW hWL hfW himage hstep

end SurfaceDynamics

#print axioms SurfaceDynamics.false_of_positive_area_area_advances
