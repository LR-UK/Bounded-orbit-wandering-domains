import BoundedWanderingDomains.LocalTrappedTopology

open Set Function Filter TopologicalSpace
open scoped Topology

namespace AreaDeficit

/-- Finite outer root sets can be chosen increasingly, with prescribed
anchors, and dense in the complement of the working domain. -/
theorem exists_outer_root_sequence {V : Set ℂ} {a b : ℂ}
    (ha : a ∉ V) (hb : b ∉ V) :
    ∃ Q : ℕ → Finset ℂ, Monotone Q ∧ (∀ n, a ∈ Q n ∧ b ∈ Q n) ∧
      (∀ n, Disjoint (↑(Q n) : Set ℂ) V) ∧
      Vᶜ ⊆ closure (⋃ n, (↑(Q n) : Set ℂ)) := by
  classical
  obtain ⟨S, hS, hSV, hd⟩ := exists_countable_dense_subset Vᶜ
  obtain ⟨q, hq⟩ := (hS.insert a).exists_eq_range ⟨a, mem_insert a S⟩
  let Q : ℕ → Finset ℂ := fun n => {a, b} ∪ (Finset.range (n + 1)).image q
  have hm : Monotone Q := by
    intro n m hnm
    exact Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.image_subset_image (Finset.range_mono (Nat.succ_le_succ hnm)))
  refine ⟨Q, hm, ?_, ?_, ?_⟩
  · intro n
    simp [Q]
  · intro n
    apply disjoint_left.mpr
    intro x hx hxV
    rcases Finset.mem_union.mp hx with hx | hx
    · have h := Finset.mem_insert.mp hx
      rcases h with rfl | h
      · exact ha hxV
      · have he : x = b := Finset.mem_singleton.mp h
        exact hb (he ▸ hxV)
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
      have hk : q k ∈ insert a S := hq ▸ mem_range_self k
      rcases hk with hka | hks
      · exact ha (hka ▸ hxV)
      · exact hSV hks hxV
  · apply hd.trans (closure_mono ?_)
    intro x hx
    obtain ⟨n, rfl⟩ := hq ▸ (mem_insert_of_mem a hx)
    exact mem_iUnion.mpr ⟨n, Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), rfl⟩)⟩

/-- A fully constructed increasing finite puncture sequence. Its limit
barrier detects exactly the non-interior trapped points. -/
theorem exists_local_puncture_sequence
    {f : ℂ → ℂ} {V L : Set ℂ} (hV : IsOpen V) (hVL : V ⊆ L)
    (hL : IsCompact L) (hf : AnalyticOnNhd ℂ f L)
    (hn : ∀ x ∈ L, ¬EventuallyConst f (𝓝 x))
    {a b : ℂ} (ha : a ∉ V) (hb : b ∉ V) :
    ∃ P : ℕ → Finset ℂ, Monotone P ∧ (∀ n, a ∈ P n ∧ b ∈ P n) ∧
      (∀ n, ∀ x ∈ V, x ∈ P n → f x ∈ P n) ∧
      (∀ n, ∀ x ∈ trappedSet f V, x ∉ P n) ∧
      trappedSet f V ∩ closure (⋃ n, (↑(P n) : Set ℂ)) =
        trappedSet f V \ interior (trappedSet f V) ∧
      frontier V ⊆ closure (⋃ n, (↑(P n) : Set ℂ)) ∧
      V ∩ f ⁻¹' closure (⋃ n, (↑(P n) : Set ℂ)) ⊆
        closure (⋃ n, (↑(P n) : Set ℂ)) := by
  classical
  obtain ⟨Q, hQ, hab, hQV, hdense⟩ := exists_outer_root_sequence ha hb
  let R : ℕ → Set ℂ := fun n => ↑(Q n)
  have hR : Monotone R := fun _ _ h => hQ h
  have hfin := analytic_localPunctures_finite hVL hL hf hn (fun n => (Q n).finite_toSet)
  let P : ℕ → Finset ℂ := fun n => (hfin n).toFinset
  have hcoe : ∀ n, (↑(P n) : Set ℂ) = localPunctures f V R n :=
    fun n => (hfin n).coe_toFinset
  refine ⟨P, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n m hnm
    simpa only [← Finset.coe_subset, hcoe] using localPunctures_mono hR hnm
  · intro n
    have hroot := roots_subset_backwardTree f V (R n) n
    exact ⟨(hfin n).mem_toFinset.mpr (hroot (hab n).1),
      (hfin n).mem_toFinset.mpr (hroot (hab n).2)⟩
  · intro n x hx hxP
    apply (hfin n).mem_toFinset.mpr
    exact backwardTree_forward (hQV n) n ⟨x, ⟨(hfin n).mem_toFinset.mp hxP, hx⟩, rfl⟩
  · intro n x hx hxP
    exact trapped_not_mem_backwardTree (hQV n) hx n ((hfin n).mem_toFinset.mp hxP)
  · simp_rw [hcoe]
    apply analytic_trapped_inter_puncture_closure hV (hf.mono hVL)
      (fun x hx => hn x (hVL hx)) hR hQV
    exact (fun x hx => hdense (by simpa [hV.interior_eq] using hx.2))
  · simp_rw [hcoe]
    apply (show frontier V ⊆ closure (⋃ n, R n) from
      fun x hx => hdense (by simpa [hV.interior_eq] using hx.2)).trans
    apply closure_mono
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n, roots_subset_backwardTree f V (R n) n hn⟩
  · simp_rw [hcoe]
    exact analytic_puncture_closure_backward_invariant hV (hf.mono hVL)
      (fun x hx => hn x (hVL hx)) hR

end AreaDeficit

#print axioms AreaDeficit.exists_local_puncture_sequence
