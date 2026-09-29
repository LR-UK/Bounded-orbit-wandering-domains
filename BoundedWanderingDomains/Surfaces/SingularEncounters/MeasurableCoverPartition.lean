module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Order.Disjointed

@[expose] public section

/-! # A measurable disjoint partition subordinate to a countable cover -/

open Set Function MeasureTheory

namespace SurfaceDynamics

theorem measurable_partition_of_countable_cover
    {X : Type*} [MeasurableSpace X] {W : Set X} (hW : MeasurableSet W)
    (B : ℕ → Set X) (hB : ∀ n, MeasurableSet (B n)) (hcover : W ⊆ ⋃ n, B n) :
    ∃ A : ℕ → Set X, (∀ n, MeasurableSet (A n)) ∧ Pairwise (Disjoint on A) ∧
      (∀ n, A n ⊆ B n) ∧ (⋃ n, A n) = W := by
  refine ⟨fun n => W ∩ disjointed B n,
    fun n => hW.inter (MeasurableSet.disjointed hB n), ?_, ?_, ?_⟩
  · exact fun _ _ hnm => (disjoint_disjointed B hnm).mono inter_subset_right inter_subset_right
  · exact fun n => inter_subset_right.trans (disjointed_subset B n)
  · simp only [← inter_iUnion, iUnion_disjointed]
    exact inter_eq_left.mpr hcover

end SurfaceDynamics
