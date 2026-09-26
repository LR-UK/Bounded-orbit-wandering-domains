/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DomainAreaBlowup
import BoundedWanderingDomains.Surfaces.PositiveAreaBridge

/-! # The final contradiction from uniformly bounded finite models -/

open Set MeasureTheory
open scoped Manifold ENNReal

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- Measure-theoretic form of the final contradiction. -/
theorem false_of_positive_hyperbolicArea_finite_model_bounds
    (p : AreaDeficit.Surfaces.DiscCover X)
    (P : ℕ → Finset X) (hP : Monotone P) {A : Set X}
    (hA : MeasurableSet A) (hApos : 0 < p.hyperbolicArea A)
    (hAP : A ⊆ closure (⋃ n, (P n : Set X)))
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ n, p.domainArea
      (AreaDeficit.Surfaces.finitePunctureDomain (P n)) A ≤ C) : False := by
  have hzero : p.hyperbolicArea A = 0 :=
    p.measure_zero_of_finite_model_area_bounds P hP hA hAP hC hbound
  exact (ne_of_gt hApos) hzero

/-- Once the boundary punctures are dense on the measured set, a uniform
finite-model area budget contradicts positive chart area.  This is the final
Fatou step of the positive-area argument, separated from dynamical transport. -/
theorem false_of_positive_area_finite_model_bounds
    (p : AreaDeficit.Surfaces.DiscCover X)
    (P : ℕ → Finset X) (hP : Monotone P) {A : Set X}
    (hA : MeasurableSet A) (hApos : HasPositiveChartArea A)
    (hAP : A ⊆ closure (⋃ n, (P n : Set X)))
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ n, p.domainArea
      (AreaDeficit.Surfaces.finitePunctureDomain (P n)) A ≤ C) : False := by
  have hpos : 0 < p.hyperbolicArea A :=
    hApos.hyperbolicArea_pos hA p
  exact false_of_positive_hyperbolicArea_finite_model_bounds
    p P hP hA hpos hAP hC hbound

end SurfaceDynamics

#print axioms SurfaceDynamics.false_of_positive_area_finite_model_bounds
#print axioms SurfaceDynamics.false_of_positive_hyperbolicArea_finite_model_bounds
