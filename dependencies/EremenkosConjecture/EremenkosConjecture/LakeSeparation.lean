import EremenkosConjecture.WadaStages

open Set Metric Function

namespace EremenkosConjecture

theorem interior_finite_disjoint_union {ι : Type*} (s : Finset ι) (K : ι → Set ℂ)
    (hclosed : ∀ i ∈ s, IsClosed (K i))
    (hdisjoint : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (K i) (K j)) :
    interior (⋃ i ∈ s, K i) = ⋃ i ∈ s, interior (K i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.set_biUnion_insert, Finset.set_biUnion_insert]
    have hsc : IsClosed (⋃ j ∈ s, K j) := isClosed_biUnion_finset
      (fun j hj => hclosed j (Finset.mem_insert_of_mem hj))
    have hdis : Disjoint (closure (K i)) (closure (⋃ j ∈ s, K j)) := by
      rw [(hclosed i (Finset.mem_insert_self _ _)).closure_eq, hsc.closure_eq]
      apply disjoint_iUnion_right.mpr
      intro j
      apply disjoint_iUnion_right.mpr
      intro hj
      exact hdisjoint i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (fun H => hi (H.symm ▸ hj))
    rw [interior_union_of_disjoint_closure hdis]
    rw [ih (fun j hj => hclosed j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk => hdisjoint j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))]

namespace LakeConfiguration

theorem interior_obstacles {n : ℕ} (C : LakeConfiguration n) :
    interior C.obstacles = ⋃ i, (C.lake i).inside := by
  simpa only [obstacles, Finset.mem_univ, iUnion_true, AmbientDisk.interior_carrier] using
    interior_finite_disjoint_union Finset.univ (fun i => (C.lake i).carrier)
      (fun i _ => (C.lake i).compact.isClosed) (fun i _ j _ hij => C.disjoint hij)

theorem disjoint_waters {n : ℕ} (C : LakeConfiguration n) : Pairwise (Disjoint on C.water) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
      apply Set.disjoint_left.mpr
      intro z hzsea hzlake
      exact hzsea (C.outer.inside_subset (C.inside j ((C.lake j).inside_subset hzlake)))
  | some i =>
    cases j with
    | none =>
      apply Set.disjoint_left.mpr
      intro z hzlake hzsea
      exact hzsea (C.outer.inside_subset (C.inside i ((C.lake i).inside_subset hzlake)))
    | some j =>
      exact (C.disjoint (fun H => hij (congrArg some H))).mono
        (C.lake i).inside_subset (C.lake j).inside_subset

theorem disjoint_land_water {n : ℕ} (C : LakeConfiguration n) (i : Option (Fin n)) :
    Disjoint C.land (C.water i) := by
  apply Set.disjoint_left.mpr
  intro z hz hzwater
  cases i with
  | none => exact hzwater hz.1
  | some i =>
    apply hz.2
    rw [C.interior_obstacles]
    exact mem_iUnion.mpr ⟨i, hzwater⟩

theorem exists_water_of_not_land {n : ℕ} (C : LakeConfiguration n) {z : ℂ} (hz : z ∉ C.land) :
    ∃ i, z ∈ C.water i := by
  by_cases hzM : z ∈ C.outer.carrier
  · have hzA : z ∈ interior C.obstacles := by
      by_contra H
      exact hz ⟨hzM, H⟩
    rw [C.interior_obstacles] at hzA
    obtain ⟨i, hi⟩ := mem_iUnion.mp hzA
    exact ⟨some i, hi⟩
  · exact ⟨none, hzM⟩

end LakeConfiguration

end EremenkosConjecture
