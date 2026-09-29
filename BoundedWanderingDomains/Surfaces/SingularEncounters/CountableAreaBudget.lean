module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section

/-! # Summing local area costs over countably many inverse components

Disjoint target pieces use each of finitely many gain measures only once.
There is no error term proportional to the number of inverse components.
-/

open Set Function MeasureTheory
open scoped ENNReal

namespace AreaDeficit

theorem tsum_selected_measure_le_finite_budget
    {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : ι → Measure X) (A : ℕ → Set X) (label : ℕ → ι) (L : ι → Set X)
    (hA : ∀ n, MeasurableSet (A n)) (hL : ∀ i, MeasurableSet (L i))
    (hdis : Pairwise (Disjoint on A)) (hsub : ∀ n, A n ⊆ L (label n)) :
    (∑' n, μ (label n) (A n)) ≤ ∑ i, μ i (L i) := by
  classical
  have hsum : ∀ n, μ (label n) (A n) ≤ ∑ i, μ i (A n ∩ L i) := by
    intro n
    have he : A n ∩ L (label n) = A n := inter_eq_left.mpr (hsub n)
    calc
      μ (label n) (A n) = μ (label n) (A n ∩ L (label n)) := by rw [he]
      _ ≤ ∑ i, μ i (A n ∩ L i) :=
        Finset.single_le_sum (f := fun i => μ i (A n ∩ L i))
          (fun _ _ => bot_le) (Finset.mem_univ (label n))
  have hbudget : ∀ i, (∑' n, μ i (A n ∩ L i)) ≤ μ i (L i) := by
    intro i
    have hdis' : Pairwise (Disjoint on fun n => A n ∩ L i) := by
      intro n m hnm
      exact (hdis hnm).mono inter_subset_left inter_subset_left
    rw [← measure_iUnion hdis' (fun n => (hA n).inter (hL i))]
    exact measure_mono (iUnion_subset fun _ => inter_subset_right)
  calc
    (∑' n, μ (label n) (A n)) ≤ ∑' n, ∑ i, μ i (A n ∩ L i) :=
      ENNReal.tsum_le_tsum hsum
    _ = ∑ i, ∑' n, μ i (A n ∩ L i) := by
      simp only [← tsum_fintype (L := SummationFilter.unconditional ι)]
      exact ENNReal.tsum_comm
    _ ≤ ∑ i, μ i (L i) := Finset.sum_le_sum fun i _ => hbudget i

theorem area_advance_of_countable_local_budgets
    {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ ν : Measure X) (gain : ι → Measure X)
    (A B : ℕ → Set X) (label : ℕ → ι) (L : ι → Set X)
    (hA : ∀ n, MeasurableSet (A n)) (hB : ∀ n, MeasurableSet (B n))
    (hL : ∀ i, MeasurableSet (L i))
    (hdisA : Pairwise (Disjoint on A)) (hdisB : Pairwise (Disjoint on B))
    (hsub : ∀ n, B n ⊆ L (label n))
    (hstep : ∀ n, μ (A n) ≤ ν (B n) + gain (label n) (B n)) :
    μ (⋃ n, A n) ≤ ν (⋃ n, B n) + ∑ i, gain i (L i) := by
  rw [measure_iUnion hdisA hA, measure_iUnion hdisB hB]
  calc
    (∑' n, μ (A n)) ≤ ∑' n, (ν (B n) + gain (label n) (B n)) :=
      ENNReal.tsum_le_tsum hstep
    _ = (∑' n, ν (B n)) + ∑' n, gain (label n) (B n) := ENNReal.tsum_add
    _ ≤ (∑' n, ν (B n)) + ∑ i, gain i (L i) :=
      add_le_add le_rfl
        (tsum_selected_measure_le_finite_budget gain B label L hB hL hdisB hsub)

end AreaDeficit
