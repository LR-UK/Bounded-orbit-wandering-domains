import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Connected.Clopen

open Set

namespace FunctionTheory

set_option autoImplicit false

/-- A connected subset of a locally finite disjoint closed union lies in
one member, as soon as it meets that member. -/
theorem preconnected_subset_member_of_locallyFinite_disjoint_closed
    {E I : Type*} [TopologicalSpace E] (K : I → Set E)
    (hK : ∀ i, IsClosed (K i)) (hloc : LocallyFinite K)
    (hdis : Pairwise (fun i j => Disjoint (K i) (K j)))
    {S : Set E} (hS : IsPreconnected S) (hSK : S ⊆ ⋃ i, K i)
    {i : I} {x : E} (hxS : x ∈ S) (hxK : x ∈ K i) :
    S ⊆ K i := by
  classical
  let O : Set E := ⋃ j : {j : I // j ≠ i}, K j
  have hO : IsClosed O :=
    (hloc.comp_injective (g := fun j : {j : I // j ≠ i} => (j : I))
      Subtype.val_injective).isClosed_iUnion (fun j => hK j)
  have hKO : Disjoint (K i) O := by
    apply disjoint_left.mpr
    intro z hzi hzO
    obtain ⟨j, hj⟩ := mem_iUnion.mp hzO
    exact disjoint_left.mp (hdis j.property) hj hzi
  have hcover : S ⊆ K i ∪ O := by
    intro z hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hSK hz)
    by_cases he : j = i
    · exact Or.inl (he ▸ hj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, he⟩, hj⟩)
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hS (K i) O (hK i) hO
      hcover (by rw [hKO.inter_eq, inter_empty]) with h | h
  · exact h
  · exact False.elim (disjoint_left.mp hKO hxK (h hxS))

end FunctionTheory
