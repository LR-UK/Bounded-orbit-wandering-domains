/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.FinitePunctureInsertion

/-! # From a global one-point cost to bounded finite insertion

This file isolates the exact global analytic estimate still needed for the
finite-type compact-surface argument.  Once adding one point costs at most a
fixed amount on the whole surface, the finite-set estimate follows by
telescoping, with no subtraction of infinite measures.
-/

open Set MeasureTheory
open scoped Manifold ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]
  [LocallyCompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [DecidableEq M]

/-- A uniform whole-surface cost for adding one point to an arbitrary
finite-puncture model.  The intended sharp constant is `2 * π`. -/
def UniformGlobalPointInsertionBound (p : DiscCover M) (C : ℝ≥0∞) : Prop :=
  ∀ (P : Finset M) (a : M),
    p.domainAreaGain (finitePunctureDomain P)
      (finitePunctureDomain (insert a P)) Set.univ ≤ C

/-- A uniform one-point whole-surface estimate telescopes to a bound for
inserting any finite set. -/
theorem global_finitePuncture_gain_le_of_pointInsertion
    (p : DiscCover M) {C : ℝ≥0∞}
    (hpoint : p.UniformGlobalPointInsertionBound C) :
    ∀ (P E : Finset M),
      p.domainAreaGain (finitePunctureDomain P)
          (finitePunctureDomain (P ∪ E)) Set.univ ≤
        (E.card : ℝ≥0∞) * C := by
  intro P E
  induction E using Finset.induction_on with
  | empty => simp [p.domainAreaGain_self]
  | @insert a E ha ih =>
      calc
        p.domainAreaGain (finitePunctureDomain P)
            (finitePunctureDomain (P ∪ insert a E)) Set.univ ≤
            p.domainAreaGain (finitePunctureDomain P)
                (finitePunctureDomain (P ∪ E)) Set.univ +
              p.domainAreaGain (finitePunctureDomain (P ∪ E))
                (finitePunctureDomain (insert a (P ∪ E))) Set.univ := by
                  simpa only [Finset.union_insert] using
                    p.domainAreaGain_triangle
                      (finitePunctureDomain P)
                      (finitePunctureDomain (P ∪ insert a E))
                      (finitePunctureDomain (P ∪ E)) MeasurableSet.univ
        _ ≤ (E.card : ℝ≥0∞) * C + C :=
          add_le_add ih (hpoint (P ∪ E) a)
        _ = ((insert a E).card : ℝ≥0∞) * C := by
          rw [Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one,
            add_mul, one_mul]

/-- The measure form used by the global cancellation package. -/
theorem uniform_global_finitePuncture_insertion_area_le_of_pointInsertion
    (p : DiscCover M) (q : ℕ) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hpoint : p.UniformGlobalPointInsertionBound C) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧
      ∀ (P E : Finset M), E.card ≤ q →
        ∀ A : Set M, MeasurableSet A →
          p.domainArea (finitePunctureDomain (P ∪ E)) A ≤
            p.domainArea (finitePunctureDomain P) A + D := by
  refine ⟨(q : ℝ≥0∞) * C,
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top q) hC, ?_⟩
  intro P E hEq A hA
  refine (p.domainArea_le_add_gain (finitePunctureDomain P)
    (finitePunctureDomain (P ∪ E)) hA).trans ?_
  have hgain :
      p.domainAreaGain (finitePunctureDomain P)
          (finitePunctureDomain (P ∪ E)) A ≤ (q : ℝ≥0∞) * C :=
    (measure_mono (subset_univ A)).trans
      ((p.global_finitePuncture_gain_le_of_pointInsertion hpoint P E).trans (by
        gcongr))
  exact add_le_add_right hgain _

end AreaDeficit.Surfaces.DiscCover

#print axioms AreaDeficit.Surfaces.DiscCover.global_finitePuncture_gain_le_of_pointInsertion
#print axioms AreaDeficit.Surfaces.DiscCover.uniform_global_finitePuncture_insertion_area_le_of_pointInsertion
