import Mathlib.Topology.Connected.Basic
import EremenkosConjecture.BoundarySelection

/-! # Closed barriers isolate connected components

These lemmas do not require the barriers to be bounded. They apply to the
nested half-strips used in Section 7, in contrast to path-only barriers.
-/

open Set

namespace EremenkosConjecture

variable {X : Type*} [TopologicalSpace X]

theorem connectedComponentIn_subset_interior_of_frontier_disjoint
    {A B : Set X} (hB : IsClosed B) (hfront : Disjoint A (frontier B))
    {z : X} (hzA : z ∈ A) (hzB : z ∈ interior B) :
    connectedComponentIn A z ⊆ interior B := by
  have hsub : connectedComponentIn A z ⊆ interior B ∪ Bᶜ := by
    intro w hw
    by_cases hwB : w ∈ B
    · apply Or.inl
      by_contra hwi
      exact Set.disjoint_left.mp hfront (connectedComponentIn_subset A z hw)
        ⟨hB.closure_eq.symm ▸ hwB, hwi⟩
    · exact Or.inr hwB
  exact isPreconnected_connectedComponentIn.subset_left_of_subset_union
    isOpen_interior hB.isOpen_compl (disjoint_compl_right.mono_left interior_subset)
    hsub ⟨z, mem_connectedComponentIn hzA, hzB⟩

/-- A family of closed neighbourhoods with boundaries outside `A` isolates
the connected set given by their intersection as an actual connected
component of `A`. Neither compactness nor local connectedness is assumed. -/
theorem connectedComponentIn_eq_of_closed_barriers {ι : Type*}
    {A K : Set X} {B : ι → Set X} (hK : IsPreconnected K) (hKA : K ⊆ A)
    (hB : ∀ i, IsClosed (B i)) (hinside : ∀ i, K ⊆ interior (B i))
    (hinter : ⋂ i, B i = K) (hfront : ∀ i, Disjoint A (frontier (B i)))
    {z : X} (hz : z ∈ K) : connectedComponentIn A z = K := by
  apply Subset.antisymm
  · intro w hw
    rw [← hinter]
    exact mem_iInter.mpr fun i => interior_subset
      (connectedComponentIn_subset_interior_of_frontier_disjoint
        (hB i) (hfront i) (hKA hz) (hinside i hz) hw)
  · exact hK.subset_connectedComponentIn hz hKA

/-- The same barriers isolate a singleton in a smaller set that meets the
intersection in only that point. This is a connected-component conclusion. -/
theorem connectedComponentIn_eq_singleton_of_closed_barriers {ι : Type*}
    {A K : Set X} {B : ι → Set X} {z : X} (hzA : z ∈ A) (hzK : z ∈ K)
    (hB : ∀ i, IsClosed (B i)) (hinside : ∀ i, K ⊆ interior (B i))
    (hinter : ⋂ i, B i = K) (hfront : ∀ i, Disjoint A (frontier (B i)))
    (hmeet : A ∩ K ⊆ {z}) : connectedComponentIn A z = {z} := by
  apply Subset.antisymm
  · intro w hw
    apply hmeet
    refine ⟨connectedComponentIn_subset A z hw, ?_⟩
    rw [← hinter]
    exact mem_iInter.mpr fun i => interior_subset
      (connectedComponentIn_subset_interior_of_frontier_disjoint
        (hB i) (hfront i) hzA (hinside i hzK) hw)
  · exact singleton_subset_iff.mpr (mem_connectedComponentIn hzA)

end EremenkosConjecture

namespace EremenkosConjecture

/-- Boundaries of closed neighbourhoods accumulate on the boundary of their
intersection. This version does not require compact neighbourhoods. -/
theorem frontier_subset_closure_union_frontiers {ι : Type*} {K : Set ℂ}
    (hK : IsClosed K) (B : ι → Set ℂ) (hB : ∀ i, IsClosed (B i))
    (hKB : ∀ i, K ⊆ B i) (hinter : ⋂ i, B i = K) :
    frontier K ⊆ closure (⋃ i, frontier (B i)) := by
  intro z hz
  have hzK : z ∈ K := hK.closure_eq ▸ hz.1
  have hzc : z ∈ closure Kᶜ := by
    rw [frontier_eq_closure_inter_closure] at hz
    exact hz.2
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨w, hw, hzw⟩ := Metric.mem_closure_iff.mp hzc ε hε
  have hex : ∃ i, w ∉ B i := by
    by_contra! h
    exact hw (hinter ▸ mem_iInter.mpr h)
  obtain ⟨i, hi⟩ := hex
  obtain ⟨q, hq, hzq⟩ := exists_frontier_near_of_mem_of_not_mem (B i) (hB i)
    (hKB i hzK) hi hε hzw
  exact ⟨q, mem_iUnion.mpr ⟨i, hq⟩, hzq⟩

end EremenkosConjecture
