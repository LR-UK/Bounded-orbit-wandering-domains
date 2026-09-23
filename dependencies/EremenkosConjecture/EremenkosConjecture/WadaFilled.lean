import EremenkosConjecture.WadaLimits

open Set Metric Function

namespace EremenkosConjecture.WadaConstruction

def filled (W : WadaConstruction) : Set ℂ := (W.domain none)ᶜ

theorem filled_eq_inter (W : WadaConstruction) : W.filled = ⋂ n, W.island n := by
  ext z
  simp only [filled, domain, waterAt, mem_compl_iff, mem_iUnion, not_exists, not_not, mem_iInter]

theorem compact_filled (W : WadaConstruction) : IsCompact W.filled := by
  rw [W.filled_eq_inter]
  exact (W.stage 0).outer.compact.of_isClosed_subset
    (isClosed_iInter (fun n => (W.stage n).outer.compact.isClosed)) (iInter_subset _ 0)

theorem connected_filled (W : WadaConstruction) : IsConnected W.filled := by
  rw [W.filled_eq_inter]
  exact isConnected_nested_inter (fun n => (W.stage n).outer.compact)
    (fun n => (W.stage n).outer.connected) W.island_antitone

theorem full_filled (W : WadaConstruction) : IsConnected W.filledᶜ := by
  simpa only [filled, compl_compl] using W.connected_domain none

theorem frontier_filled (W : WadaConstruction) : frontier W.filled = W.boundary := by
  rw [filled, frontier_compl, W.frontier_domain]

theorem domain_subset_filled (W : WadaConstruction) (i : ℕ) : W.domain (some i) ⊆ W.filled := by
  intro z hz hsea
  exact Set.disjoint_left.mp (W.disjoint_domains (show some i ≠ none by simp)) hz hsea

theorem domain_subset_interior_filled (W : WadaConstruction) (i : ℕ) :
    W.domain (some i) ⊆ interior W.filled :=
  (W.open_domain (some i)).subset_interior_iff.mpr (W.domain_subset_filled i)

theorem interior_filled_eq (W : WadaConstruction) : interior W.filled = ⋃ i : ℕ, W.domain (some i) := by
  apply Subset.antisymm
  · intro z hz
    have hzX : z ∉ W.boundary := by
      rw [← W.frontier_filled]
      exact fun H => H.2 hz
    obtain ⟨i, hi⟩ := W.exists_domain_of_not_boundary hzX
    cases i with
    | none => exact ((interior_subset hz) hi).elim
    | some i => exact mem_iUnion.mpr ⟨i, hi⟩
  · exact iUnion_subset (fun i => W.domain_subset_interior_filled i)

theorem connectedComponentIn_interior_filled (W : WadaConstruction) (i : ℕ) {x : ℂ}
    (hx : x ∈ W.domain (some i)) :
    connectedComponentIn (interior W.filled) x = W.domain (some i) := by
  have hxint := W.domain_subset_interior_filled i hx
  apply Subset.antisymm
  · have hsub : connectedComponentIn (interior W.filled) x ⊆
        W.domain (some i) ∪ (closure (W.domain (some i)))ᶜ := by
      intro z hz
      by_cases hzi : z ∈ W.domain (some i)
      · exact Or.inl hzi
      · right
        intro hzcl
        have hzfront : z ∈ frontier (W.domain (some i)) := ⟨hzcl, fun H => hzi (interior_subset H)⟩
        rw [W.frontier_domain, ← W.frontier_filled] at hzfront
        exact hzfront.2 (connectedComponentIn_subset _ _ hz)
    exact isPreconnected_connectedComponentIn.subset_left_of_subset_union
      (W.open_domain (some i)) isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left subset_closure) hsub
      ⟨x, mem_connectedComponentIn hxint, hx⟩
  · exact (W.connected_domain (some i)).isPreconnected.subset_connectedComponentIn hx
      (W.domain_subset_interior_filled i)

theorem bounded_domain (W : WadaConstruction) (i : ℕ) : Bornology.IsBounded (W.domain (some i)) :=
  W.compact_filled.isBounded.subset (W.domain_subset_filled i)

theorem injective_domains (W : WadaConstruction) : Injective (fun i : ℕ => W.domain (some i)) := by
  intro i j hij
  change W.domain (some i) = W.domain (some j) at hij
  by_contra hne
  obtain ⟨z, hz⟩ := (W.connected_domain (some i)).nonempty
  have hd := W.disjoint_domains (show some i ≠ some j from fun H => hne (Option.some.inj H))
  exact Set.disjoint_left.mp hd hz (hij ▸ hz)

end EremenkosConjecture.WadaConstruction
