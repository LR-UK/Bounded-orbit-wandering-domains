import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Data.Finset.Basic

open Set

namespace EremenkosConjecture

/-- A loop in a path-connected set can visit any prescribed finite subset. -/
theorem exists_loop_through_finset {α : Type*} [TopologicalSpace α]
    {U : Set α} (hU : IsPathConnected U) {a : α} (ha : a ∈ U)
    (s : Finset α) (hs : (s : Set α) ⊆ U) :
    ∃ γ : Path a a, range γ ⊆ U ∧ (s : Set α) ⊆ range γ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨Path.refl a, by simpa using singleton_subset_iff.mpr ha, by simp⟩
  | @insert b s hbs ih =>
    obtain ⟨γ, hγ, hsγ⟩ := ih (fun x hx => hs (Finset.mem_insert_of_mem hx))
    obtain ⟨β, hβ⟩ := hU.joinedIn a ha b (hs (Finset.mem_insert_self b s))
    refine ⟨γ.trans (β.trans β.symm), ?_, ?_⟩
    · rw [Path.trans_range, Path.trans_range, Path.symm_range, union_self]
      exact union_subset hγ (range_subset_iff.mpr hβ)
    · rw [Path.trans_range, Path.trans_range, Path.symm_range, union_self]
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Or.inr β.target_mem_range
      · exact Or.inl (hsγ hx)

end EremenkosConjecture
