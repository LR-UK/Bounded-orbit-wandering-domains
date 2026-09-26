/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.PositiveAreaAdvanceReduction

/-! # Global finite-puncture area packages -/

open Set MeasureTheory
open scoped Manifold ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]
  [LocallyCompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [DecidableEq M]

/-- The two global geometric facts required when the measured wandering
union need not lie in a compact subset of the hyperbolic ambient surface:
every finite-puncture model has finite total area, and inserting at most `q`
points has one uniform area cost. -/
def GlobalFinitePunctureAreaPackage (p : DiscCover M) (q : ℕ) : Prop :=
  ∃ D : ℝ≥0∞, D ≠ ⊤ ∧
    (∀ P : Finset M,
      p.domainArea (finitePunctureDomain P) Set.univ ≠ ⊤) ∧
    ∀ (P E : Finset M), E.card ≤ q →
      ∀ A : Set M, MeasurableSet A →
        p.domainArea (finitePunctureDomain (P ∪ E)) A ≤
          p.domainArea (finitePunctureDomain P) A + D

/-- On a compact hyperbolic ambient surface the global package follows
from compact local finiteness and the uniform finite-removal estimate. -/
theorem globalFinitePunctureAreaPackage_of_compact [CompactSpace M]
    (p : DiscCover M) (q : ℕ) :
    p.GlobalFinitePunctureAreaPackage q := by
  obtain ⟨D, hD, hinsert⟩ :=
    p.uniform_finitePuncture_insertion_area_le q
      (isCompact_univ : IsCompact (Set.univ : Set M))
  refine ⟨D, hD, fun P => ?_, ?_⟩
  · exact (p.finitePunctureDomain_area_compact_finite P
      (isCompact_univ : IsCompact (Set.univ : Set M))).ne
  · intro P E hEq A hA
    exact hinsert P E hEq A hA (subset_univ A)

/-- On any finite-area hyperbolic surface, the total-area part of the global
package is automatic.  Thus only the uniform insertion estimate remains to
be supplied. -/
theorem globalFinitePunctureAreaPackage_of_finite_total
    (p : DiscCover M) (q : ℕ)
    (htotal : p.hyperbolicArea Set.univ < ⊤)
    (hinsert : ∃ D : ℝ≥0∞, D ≠ ⊤ ∧
      ∀ (P E : Finset M), E.card ≤ q →
        ∀ A : Set M, MeasurableSet A →
          p.domainArea (finitePunctureDomain (P ∪ E)) A ≤
            p.domainArea (finitePunctureDomain P) A + D) :
    p.GlobalFinitePunctureAreaPackage q := by
  obtain ⟨D, hD, hcost⟩ := hinsert
  refine ⟨D, hD, ?_, hcost⟩
  intro P
  exact (p.finitePunctureDomain_area_univ_finite_of_hyperbolicArea_univ_finite
    P htotal).ne

end AreaDeficit.Surfaces.DiscCover

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [SecondCountableTopology X]
  [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [DecidableEq X]

/-- A global finite-area package turns the one-step area inequality directly
into the intrinsic positive-area contradiction, without compact containment
in the punctured ambient surface. -/
theorem false_of_positive_hyperbolicArea_global_package
    (p : AreaDeficit.Surfaces.DiscCover X) (q : ℕ)
    (hp : p.GlobalFinitePunctureAreaPackage q)
    (P : ℕ → Finset X) (hP : Monotone P) {A : Set X}
    (hA : MeasurableSet A) (hApos : 0 < p.hyperbolicArea A)
    (hAP : A ⊆ closure (⋃ n, (P n : Set X)))
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hadvance : ∀ n, ∃ (E : Finset X) (f : X → X) (W : Set X),
      E.card ≤ q ∧ A ⊆ W ∧ MeasurableSet (f '' W) ∧
      f '' W ⊆ W \ A ∧
      p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain (P n)) W ≤
        p.domainArea
          (AreaDeficit.Surfaces.finitePunctureDomain (P n ∪ E)) (f '' W) + C) :
    False := by
  obtain ⟨D, hD, htotal, hcost⟩ := hp
  apply false_of_positive_hyperbolicArea_global_area_advances
    p P hP hA hApos hAP hC hD
  intro n
  obtain ⟨E, f, W, hEq, hAW, hfW, himage, hstep⟩ := hadvance n
  refine ⟨E, f, W, hAW, hfW, himage, ?_, hstep, hcost (P n) E hEq _ hfW⟩
  exact ne_top_of_le_ne_top (htotal (P n)) (measure_mono (subset_univ W))

/-- Chart-positive version of the global package reduction. -/
theorem false_of_positive_area_global_package
    (p : AreaDeficit.Surfaces.DiscCover X) (q : ℕ)
    (hp : p.GlobalFinitePunctureAreaPackage q)
    (P : ℕ → Finset X) (hP : Monotone P) {A : Set X}
    (hA : MeasurableSet A) (hApos : HasPositiveChartArea A)
    (hAP : A ⊆ closure (⋃ n, (P n : Set X)))
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hadvance : ∀ n, ∃ (E : Finset X) (f : X → X) (W : Set X),
      E.card ≤ q ∧ A ⊆ W ∧ MeasurableSet (f '' W) ∧
      f '' W ⊆ W \ A ∧
      p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain (P n)) W ≤
        p.domainArea
          (AreaDeficit.Surfaces.finitePunctureDomain (P n ∪ E)) (f '' W) + C) :
    False := by
  exact false_of_positive_hyperbolicArea_global_package p q hp P hP hA
    (hApos.hyperbolicArea_pos hA p) hAP hC hadvance

end SurfaceDynamics

#print axioms SurfaceDynamics.false_of_positive_area_global_package
#print axioms SurfaceDynamics.false_of_positive_hyperbolicArea_global_package
#print axioms AreaDeficit.Surfaces.DiscCover.globalFinitePunctureAreaPackage_of_compact
#print axioms AreaDeficit.Surfaces.DiscCover.globalFinitePunctureAreaPackage_of_finite_total
