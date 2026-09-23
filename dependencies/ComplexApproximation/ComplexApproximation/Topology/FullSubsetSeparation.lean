import ComplexApproximation.Topology.FullCompactSets
import FunctionTheory.Topology.LocallyFiniteSeparation
import FunctionTheory.Topology.LocallyFiniteCompactFamily

open Set Filter Metric Bornology
open scoped Topology

namespace ComplexApproximation

set_option autoImplicit false

/-- A connected unbounded complement has no bounded components. -/
theorem noBoundedComplementComponents_of_unbounded_connected_compl
    {E : Set ℂ} (hc : IsPreconnected Eᶜ) (hu : ¬ IsBounded Eᶜ) :
    NoBoundedComplementComponents E := by
  intro z hz hb
  exact hu (hb.subset (hc.subset_connectedComponentIn hz Subset.rfl))

/-- If a compact set and a disjoint closed set have no bounded holes in
their union, then the compact set is full. -/
theorem isConnected_compl_of_noBounded_disjoint_union
    (A B : Set ℂ) (hA : IsCompact A) (hB : IsClosed B)
    (hdis : Disjoint A B) (hfull : NoBoundedComplementComponents (A ∪ B)) :
    IsConnected Aᶜ := by
  apply isConnected_compl_of_unbounded_components A hA.isBounded
  intro z hz hb
  let V := connectedComponentIn Aᶜ z
  have hVB : V ⊆ B := by
    intro w hw
    by_contra hwB
    have hwE : w ∉ A ∪ B := fun h => h.elim
      (fun hA => connectedComponentIn_subset Aᶜ z hw hA) hwB
    have hsub : connectedComponentIn (A ∪ B)ᶜ w ⊆ V := by
      have H := connectedComponentIn_mono w (compl_subset_compl.mpr (subset_union_left : A ⊆ A ∪ B))
      rw [← connectedComponentIn_eq hw] at H
      exact H
    exact hfull w hwE (hb.subset hsub)
  have hVne : V ≠ univ := by
    intro h
    exact not_isBounded_exterior 1
      ((show IsBounded (univ : Set ℂ) from h ▸ hb).subset (subset_univ _))
  obtain ⟨w, hw⟩ := nonempty_frontier_iff.mpr
    ⟨⟨z, mem_connectedComponentIn hz⟩, hVne⟩
  have hwA : w ∈ A := by
    simpa only [compl_compl] using frontier_component_subset_compl hA.isClosed.isOpen_compl hz hw
  exact disjoint_left.mp hdis hwA (closure_minimal hVB hB hw.1)

/-- The complement of a locally finite disjoint compact family is
unbounded. A whole exterior cannot lie in a single compact member. -/
theorem not_isBounded_compl_locallyFinite_disjoint_compacts
    {I : Type*} (K : I → Set ℂ) (hK : ∀ i, IsCompact (K i))
    (hloc : LocallyFinite K)
    (hdis : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ¬ IsBounded (⋃ i, K i)ᶜ := by
  intro hb
  obtain ⟨R, hR, hbound⟩ := hb.exists_pos_norm_le
  have hcover : {z : ℂ | R < ‖z‖} ⊆ ⋃ i, K i := by
    intro z hz
    by_contra h
    exact (not_lt_of_ge (hbound z h)) hz
  obtain ⟨x, hx⟩ := (isConnected_exterior R hR).nonempty
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
  have hsub := FunctionTheory.preconnected_subset_member_of_locallyFinite_disjoint_closed
    K (fun i => (hK i).isClosed) hloc hdis (isConnected_exterior R hR).isPreconnected
    hcover hx hi
  exact not_isBounded_exterior R ((hK i).isBounded.subset hsub)

/-- The full-union hypothesis in the paper implies fullness of each
individual compact model, even when the models are disconnected. -/
theorem full_members_of_full_locallyFinite_disjoint_compacts
    {I : Type*} (K : I → Set ℂ) (hK : ∀ i, IsCompact (K i))
    (hloc : LocallyFinite K)
    (hdis : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hfull : IsConnected (⋃ i, K i)ᶜ) :
    ∀ i, IsConnected (K i)ᶜ := by
  classical
  have hno := noBoundedComplementComponents_of_unbounded_connected_compl
    hfull.isPreconnected (not_isBounded_compl_locallyFinite_disjoint_compacts K hK hloc hdis)
  intro i
  let B : Set ℂ := ⋃ j : {j : I // j ≠ i}, K j
  have hB : IsClosed B :=
    (hloc.comp_injective (g := fun j : {j : I // j ≠ i} => (j : I))
      Subtype.val_injective).isClosed_iUnion (fun j => (hK j).isClosed)
  have hdisB : Disjoint (K i) B := by
    apply disjoint_left.mpr
    intro z hzi hzB
    obtain ⟨j, hj⟩ := mem_iUnion.mp hzB
    exact disjoint_left.mp (hdis j.property) hj hzi
  have heq : K i ∪ B = ⋃ j, K j := by
    ext z
    constructor
    · rintro (hz | hz)
      · exact mem_iUnion.mpr ⟨i, hz⟩
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hz
        exact mem_iUnion.mpr ⟨j, hj⟩
    · intro hz
      obtain ⟨j, hj⟩ := mem_iUnion.mp hz
      by_cases he : j = i
      · exact Or.inl (he ▸ hj)
      · exact Or.inr (mem_iUnion.mpr ⟨⟨j, he⟩, hj⟩)
  exact isConnected_compl_of_noBounded_disjoint_union (K i) B (hK i) hB hdisB
    (heq.symm ▸ hno)

end ComplexApproximation
