/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.BackwardExceptionalPackage
import BoundedWanderingDomains.Surfaces.PositiveAreaBridge

/-! # Removing backward exceptional points from a positive-area set -/

open Set Function MeasureTheory
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

/-- Enlarge the boundary stages by finitely many exceptional values and all
their backward iterates.  Deleting the resulting countable union preserves
measurability and positive chart area, while retaining density in the new
finite-stage barrier. -/
theorem exists_backwardExceptional_positive_remainder
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (V : TopologicalSpace.Opens X)
    (hVcompact : IsCompact (closure (V : Set X)))
    (hVsource : closure (V : Set X) ⊆ f.source)
    (P : ℕ → Finset X) (hP : Monotone P) (E : Finset X)
    {A : Set X} (hAmeas : MeasurableSet A)
    (hApos : HasPositiveChartArea A)
    (hAP : A ⊆ closure (⋃ n, ((P n : Finset X) : Set X))) :
    ∃ S : ℕ → Finset X, Monotone S ∧
      (∀ n, (P n : Set X) ⊆ (S n : Set X) ∧
        (E : Set X) ⊆ (S n : Set X)) ∧
      (∀ x (hx : x ∈ V),
        f.map ⟨x, hVsource (subset_closure hx)⟩ ∈
            (⋃ n, ((S n : Finset X) : Set X)) →
          x ∈ (⋃ n, ((S n : Finset X) : Set X))) ∧
      MeasurableSet (A \ (⋃ n, ((S n : Finset X) : Set X))) ∧
      HasPositiveChartArea (A \ (⋃ n, ((S n : Finset X) : Set X))) ∧
      A \ (⋃ n, ((S n : Finset X) : Set X)) ⊆
        closure (⋃ n, ((S n : Finset X) : Set X)) := by
  classical
  obtain ⟨S, hSmono, hcontain, hback⟩ :=
    f.exists_backwardExceptionalFinsets hf V hVcompact hVsource P hP E
  refine ⟨S, hSmono, hcontain, hback, ?_⟩
  let Sstar : Set X := ⋃ n, ((S n : Finset X) : Set X)
  have hScount : Sstar.Countable :=
    Set.countable_iUnion fun n => (S n).finite_toSet.countable
  have hPS : (⋃ n, ((P n : Finset X) : Set X)) ⊆ Sstar := by
    intro x hx
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n, (hcontain n).1 hxn⟩
  exact ⟨hAmeas.diff hScount.measurableSet,
    hApos.diff_countable hScount,
    (sdiff_subset.trans hAP).trans (closure_mono hPS)⟩

end SurfaceDynamics.LocalMap

#print axioms SurfaceDynamics.LocalMap.exists_backwardExceptional_positive_remainder
