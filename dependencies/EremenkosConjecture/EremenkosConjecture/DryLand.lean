import EremenkosConjecture.AmbientDisks
import EremenkosConjecture.DisjointFullUnions

open Set Metric

namespace EremenkosConjecture

theorem AmbientDisk.closure_sdiff (D : AmbientDisk) {A : Set ℂ}
    (hA : IsClosed A) (hAD : A ⊆ D.inside) :
    closure (D.inside \ A) = D.carrier \ interior A := by
  apply Subset.antisymm
  · intro z hz
    have H := closure_inter_subset_inter_closure D.inside Aᶜ hz
    rw [D.closure_inside, closure_compl] at H
    exact H
  · intro z hz
    apply _root_.mem_closure_iff.mpr
    intro V hV hzV
    by_cases hzD : z ∈ D.inside
    · have hzA : z ∈ closure Aᶜ := by rw [closure_compl]; exact hz.2
      obtain ⟨w, hwV, hwA⟩ := _root_.mem_closure_iff.mp hzA (V ∩ D.inside)
        (hV.inter D.open_inside) ⟨hzV, hzD⟩
      exact ⟨w, hwV.1, hwV.2, hwA⟩
    · have hzA : z ∉ A := fun H => hzD (hAD H)
      have hzcl : z ∈ closure D.inside := D.closure_inside.symm ▸ hz.1
      obtain ⟨w, hwV, hwD⟩ := _root_.mem_closure_iff.mp hzcl (V ∩ Aᶜ)
        (hV.inter hA.isOpen_compl) ⟨hzV, hzA⟩
      exact ⟨w, hwV.1, hwD, hwV.2⟩

theorem AmbientDisk.connected_land (D : AmbientDisk) {A : Set ℂ}
    (hA : IsCompact A) (hfull : IsConnected Aᶜ) (hAD : A ⊆ D.inside) :
    IsConnected (D.carrier \ interior A) := by
  rw [← D.closure_sdiff hA.isClosed hAD]
  exact (D.pathConnected_sdiff hA hfull hAD).isConnected.closure

theorem isConnected_compl_finite_disjoint_union {ι : Type*} (s : Finset ι) (K : ι → Set ℂ)
    (hcompact : ∀ i ∈ s, IsCompact (K i)) (hfull : ∀ i ∈ s, IsConnected (K i)ᶜ)
    (hdisjoint : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (K i) (K j)) :
    IsConnected (⋃ i ∈ s, K i)ᶜ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isConnected_univ : IsConnected (univ : Set ℂ))
  | @insert i s hi ih =>
    rw [Finset.set_biUnion_insert]
    apply isConnected_compl_union_disjoint _ _ (hcompact i (Finset.mem_insert_self _ _))
      (s.isCompact_biUnion (fun j hj => hcompact j (Finset.mem_insert_of_mem hj)))
      (hfull i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hcompact j (Finset.mem_insert_of_mem hj))
        (fun j hj => hfull j (Finset.mem_insert_of_mem hj))
        (fun j hj k hk => hdisjoint j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)))
    apply disjoint_iUnion_right.mpr
    intro j
    apply disjoint_iUnion_right.mpr
    intro hj
    exact hdisjoint i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
      (fun H => hi (H.symm ▸ hj))

end EremenkosConjecture
