/- Compatibility update, 23 September 2026: current Lean linter suggestions;
mathematical statements and original attribution retained. -/

import EremenkosConjecture.SquareChainNeighbourhood

/-! # Jordan neighbourhoods from outer faces of finite plane graphs -/

open Set Metric Schoenflies
open scoped Topology Graph

namespace EremenkosConjecture

theorem jordan_fill_eq_closure_inside {C : Set Plane} (hC : IsSeparating C) :
    (outside C)ᶜ = closure (inside C) := by
  rw [closure_eq_self_union_frontier, hC.frontier_inside]
  have hpart := inside_union_outside (C := C)
  have hd := disjoint_inside_outside (C := C)
  have hi := inside_subset_compl (C := C)
  have ho := outside_subset_compl (C := C)
  ext z
  simp only [mem_compl_iff, mem_union] at *
  constructor
  · intro hz
    by_cases hzC : z ∈ C
    · exact Or.inr hzC
    · have H : z ∈ inside C ∪ outside C := hpart.symm ▸ hzC
      exact Or.inl (H.resolve_right hz)
  · rintro (hz | hz)
    · exact fun H => Set.disjoint_left.mp hd hz H
    · exact fun H => ho H hz

theorem jordan_fill_properties {C : Set Plane} (hC : IsSeparating C) :
    IsCompact (outside C)ᶜ ∧ IsConnected (outside C)ᶜ ∧
      IsConnected ((outside C)ᶜ)ᶜ ∧ frontier (outside C)ᶜ = C ∧
      interior (outside C)ᶜ = inside C := by
  have heq := jordan_fill_eq_closure_inside hC
  refine ⟨?_, ?_, by simpa using hC.isConnected_outside, ?_, ?_⟩
  · rw [heq]
    exact hC.isBounded_inside.isCompact_closure
  · rw [heq]
    exact hC.isConnected_inside.closure
  · rw [frontier_compl, hC.frontier_outside]
  · rw [interior_compl, closure_eq_self_union_frontier, hC.frontier_outside]
    have hpart := inside_union_outside (C := C)
    have hd := disjoint_inside_outside (C := C)
    ext z
    constructor
    · intro hz
      have hzC : z ∉ C := fun h => hz (Or.inr h)
      have H : z ∈ inside C ∪ outside C := hpart.symm ▸ hzC
      exact H.resolve_right (fun h => hz (Or.inl h))
    · intro hz h
      rcases h with h | h
      · exact Set.disjoint_left.mp hd hz h
      · exact inside_subset_compl hz h

theorem jordan_fill_subset_full_compact {C M : Set Plane} (hC : IsSeparating C)
    (hM : IsCompact M) (hfull : IsConnected Mᶜ) (hCM : C ⊆ M) :
    (outside C)ᶜ ⊆ M := by
  have hsub : Mᶜ ⊆ inside C ∪ outside C := by
    rw [inside_union_outside]
    exact compl_subset_compl.mpr hCM
  rcases hfull.isPreconnected.subset_or_subset hC.isOpen_inside hC.isOpen_outside
      disjoint_inside_outside hsub with hin | hout
  · obtain ⟨r, _, hr⟩ := Plane.exists_closedSquare_of_isBounded hM.isBounded
    have hbound := hC.isBounded_inside.subset hin
    exact False.elim (Plane.not_isBounded_compl_closedSquare 0 r
      (hbound.subset (compl_subset_compl.mpr hr)))
  · exact compl_subset_comm.mp hout

theorem exists_jordan_neighbourhood_within_full_compact {K M : Set Plane}
    (hK : IsCompact K) (hconn : IsConnected K) (hM : IsCompact M)
    (hfull : IsConnected Mᶜ) (hKM : K ⊆ interior M) :
    ∃ L : Set Plane, IsCompact L ∧ IsConnected L ∧ IsConnected Lᶜ ∧
      K ⊆ interior L ∧ L ⊆ M ∧ IsJordanCurve (frontier L) ∧
      IsConnected (interior L) ∧ L = closure (interior L) := by
  classical
  obtain ⟨r, N, c, hr, hstep, hcover, hsub⟩ :=
    exists_square_chain_cover hK hconn isOpen_interior hKM
  let G := familyChain c N N r 0
  have : G.Finite := familyChain_finite
  have hG : Graph.IsDrawing G segmentDrawing :=
    (familyOverlay_isDrawing hr).mono familyChain_le
  have h2 : G.IsTwoConnected := familyChain_isTwoConnected squaresTwoConnected hr
    (by simp) hstep
  have hGM : Graph.pointSet G segmentDrawing ⊆ M := by
    intro z hz
    obtain ⟨j, _, hj, hzj⟩ := exists_mem_frontier_of_mem_pointSet_familyChain hz
    have hj' : j ≤ N := by simpa using hj
    have hzsq : z ∈ Plane.closedSquare (c j) r :=
      (Plane.isClosed_closedSquare _ _).closure_eq ▸ hzj.1
    exact interior_subset (hsub j hj' hzsq)
  obtain ⟨base, hbase, hbu⟩ := Graph.exists_unbounded_face hG
  have hpoly : ∀ e ∈ E(G), IsPolygonal (Graph.edgeArc segmentDrawing e) := by
    intro e _
    rw [edgeArc_segmentDrawing]
    exact isPolygonal_segment _ _
  obtain ⟨e, u, v, D, hface⟩ := Graph.face_cycles' hG hpoly h2 base hbase
  let C := Graph.edgesCover segmentDrawing (e :: D)
  have hC : IsSeparating C := hface.isSeparating
  have hout : Graph.face G segmentDrawing base = outside C := by
    rcases hface.eq_inside_or_outside with hin | hout
    · exact False.elim (hbu (hin ▸ hC.isBounded_inside))
    · exact hout
  have hCM : C ⊆ M := (Graph.edgesCover_subset_pointSet
    (fun g hg => hface.isCycle.mem_edgeSet_cons hg)).trans hGM
  have hfill := jordan_fill_properties hC
  refine ⟨(outside C)ᶜ, hfill.1, hfill.2.1, hfill.2.2.1, ?_,
    jordan_fill_subset_full_compact hC hM hfull hCM,
    by rw [hfill.2.2.2.1]; exact hC.isJordanCurve,
    by rw [hfill.2.2.2.2]; exact hC.isConnected_inside,
    by rw [hfill.2.2.2.2]; exact jordan_fill_eq_closure_inside hC⟩
  intro x hx
  obtain ⟨j, hj, hxj⟩ := hcover x hx
  have hjG : familySquare c N r j ≤ G := by
    simpa only [G, familyChain, Nat.zero_mul] using
      (Graph.le_chainUnion (G := familyOverlay c N r) (Γ := familySquare c N r)
        (i := 0) (m := N) (p := j) (fun _ _ _ => familySquare_le) (Nat.zero_le j)
        (by simpa using hj))
  have hfr : frontier (Plane.closedSquare (c j) r) ⊆ Graph.pointSet G segmentDrawing := by
    rw [← pointSet_familySquare hr hj]
    exact Graph.pointSet_mono hjG
  have hdis : Plane.openSquare (c j) r ⊆ (outside C)ᶜ := by
    intro z hz
    rw [← hout]
    exact notMem_face_of_mem_openSquare hfr hbu hz
  exact (Plane.isOpen_openSquare _ _).subset_interior_iff.mpr hdis hxj

end EremenkosConjecture
