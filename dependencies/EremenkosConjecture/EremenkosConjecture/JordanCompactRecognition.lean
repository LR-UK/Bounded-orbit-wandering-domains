import EremenkosConjecture.JordanDomains

open Set Schoenflies

namespace EremenkosConjecture

/-- A compact set with Jordan frontier and nonempty interior is the closed
Jordan region. In particular its connectedness, fullness and regularity do
not have to be supplied separately. -/
theorem compact_with_jordan_frontier_is_closed_jordan_region {K : Set Plane}
    (hK : IsCompact K) (hne : (interior K).Nonempty)
    (hJ : IsJordanCurve (frontier K)) :
    interior K = inside (frontier K) ∧ K = closure (interior K) ∧
      IsConnected K ∧ IsConnected Kᶜ ∧ IsConnected (interior K) := by
  have hsep := jordan_curve_theorem hJ
  have hregion {S : Set Plane} (hS : IsPreconnected S)
      (hSC : S ⊆ (frontier K)ᶜ) (hmeet : (S ∩ interior K).Nonempty) :
      S ⊆ interior K := by
    apply hS.subset_of_closure_inter_subset isOpen_interior hmeet
    rintro z ⟨hzcl, hzS⟩
    by_contra hzin
    exact hSC hzS (hK.isClosed.frontier_eq ▸
      ⟨hK.isClosed.closure_subset_iff.mpr interior_subset hzcl, hzin⟩)
  have hnoOut : Disjoint (outside (frontier K)) (interior K) := by
    rw [disjoint_iff_inter_eq_empty]
    apply not_nonempty_iff_eq_empty.mp
    intro hm
    have hs := hregion hsep.isConnected_outside.isPreconnected outside_subset_compl hm
    exact hsep.not_isBounded_outside (hK.isBounded.subset (hs.trans interior_subset))
  have hint : interior K ⊆ inside (frontier K) := by
    intro z hz
    have hn : z ∉ frontier K := fun hf => (hK.isClosed.frontier_eq ▸ hf).2 hz
    have hm : z ∈ inside (frontier K) ∪ outside (frontier K) := by
      rw [inside_union_outside]
      exact hn
    exact hm.resolve_right (fun ho => disjoint_left.mp hnoOut ho hz)
  have heq : interior K = inside (frontier K) := by
    refine hint.antisymm (hregion hsep.isConnected_inside.isPreconnected inside_subset_compl ?_)
    obtain ⟨z, hz⟩ := hne
    exact ⟨z, hint hz, hz⟩
  have hreg : K = closure (interior K) := by
    apply subset_antisymm
    · intro z hz
      by_cases hzi : z ∈ interior K
      · exact subset_closure hzi
      · have hzc : z ∈ frontier K := hK.isClosed.frontier_eq ▸ ⟨hz, hzi⟩
        rw [heq]
        rw [← hsep.frontier_inside] at hzc
        exact frontier_subset_closure hzc
    · exact hK.isClosed.closure_subset_iff.mpr interior_subset
  have hcompl : Kᶜ = outside (frontier K) := by
    ext z
    constructor
    · intro hz
      have hn : z ∉ frontier K := fun hf => hz (hK.isClosed.frontier_subset hf)
      have hm : z ∈ inside (frontier K) ∪ outside (frontier K) := by
        rw [inside_union_outside]
        exact hn
      exact hm.resolve_left (fun hi => hz (interior_subset (heq.symm ▸ hi)))
    · intro hz hzk
      by_cases hzi : z ∈ interior K
      · exact disjoint_left.mp hnoOut hz hzi
      · exact hz.1 (hK.isClosed.frontier_eq ▸ ⟨hzk, hzi⟩)
  have hci : IsConnected (interior K) := heq.symm ▸ hsep.isConnected_inside
  exact ⟨heq, hreg, hreg.symm ▸ hci.closure, hcompl.symm ▸ hsep.isConnected_outside, hci⟩

theorem complex_compact_with_jordan_frontier_regular {K : Set ℂ}
    (hK : IsCompact K) (hne : (interior K).Nonempty)
    (hJ : IsComplexJordanCurve (frontier K)) :
    IsConnected K ∧ IsConnected Kᶜ ∧ IsConnected (interior K) ∧
      K = closure (interior K) := by
  let e := complexPlaneHomeomorph
  have hJp : IsJordanCurve (frontier (e '' K)) := by
    rw [← e.image_frontier]
    exact hJ
  have hnep : (interior (e '' K)).Nonempty := by
    rw [← e.image_interior]
    exact hne.image e
  obtain ⟨_, hreg, hconn, hfull, hint⟩ :=
    compact_with_jordan_frontier_is_closed_jordan_region (hK.image e.continuous) hnep hJp
  refine ⟨e.isConnected_image.mp hconn, ?_, ?_, ?_⟩
  · apply e.isConnected_image.mp
    rwa [e.image_compl]
  · apply e.isConnected_image.mp
    rwa [e.image_interior]
  · apply e.injective.image_injective
    rw [e.image_closure, e.image_interior]
    exact hreg

end EremenkosConjecture
