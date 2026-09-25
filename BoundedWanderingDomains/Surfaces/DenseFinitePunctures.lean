/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactChartPatches

/-! # Exhausting a closed complement by finite punctures -/

open Set Function
open scoped Topology
namespace AreaDeficit.Surfaces

/-- In a second countable space, a closed set is the closure of an
increasing union of finite subsets. -/
theorem closed_set_dense_finite_exhaustion {M : Type*} [TopologicalSpace M]
    [SecondCountableTopology M] {A : Set M} (hA : IsClosed A) :
    ∃ P : ℕ → Finset M, Monotone P ∧
      (∀ n, (↑(P n) : Set M) ⊆ A) ∧
      closure (⋃ n, (↑(P n) : Set M)) = A := by
  classical
  by_cases hne : A.Nonempty
  · let : Nonempty A := hne.to_subtype
    obtain ⟨u,hu⟩ := TopologicalSpace.exists_dense_seq (α := A)
    let P : ℕ → Finset M := fun n => (Finset.range (n + 1)).image (fun k => (u k : M))
    refine ⟨P,?_,?_,?_⟩
    · intro i j hij
      apply Finset.image_mono
      exact Finset.range_mono (Nat.add_le_add_right hij 1)
    · intro n x hx
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hx
      exact (u k).property
    · have hrange : (⋃ n, (↑(P n) : Set M)) =
          Set.range (fun k => (u k : M)) := by
        ext x
        constructor
        · intro hx
          obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
          obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hn
          exact ⟨k,rfl⟩
        · rintro ⟨k,rfl⟩
          exact Set.mem_iUnion.mpr ⟨k,Finset.mem_image.mpr
            ⟨k,Finset.mem_range.mpr (by omega),rfl⟩⟩
      rw [hrange]
      apply Set.Subset.antisymm
      · apply hA.closure_subset_iff.mpr
        rintro x ⟨k,rfl⟩
        exact (u k).property
      · intro x hx
        have hu' : (⟨x,hx⟩ : A) ∈ closure (Set.range u) := hu _
        have hr : (Subtype.val '' Set.range u) =
            Set.range (fun k => (u k : M)) := by
          ext z
          constructor
          · rintro ⟨y,⟨k,rfl⟩,rfl⟩
            exact ⟨k,rfl⟩
          · rintro ⟨k,rfl⟩
            exact ⟨u k,⟨k,rfl⟩,rfl⟩
        rw [← hr]
        exact closure_subtype.mp hu'
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨fun _ => ∅, monotone_const, (fun _ => by simp [he]), ?_⟩
    simp [he]

end AreaDeficit.Surfaces
