import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- A compact subset of the closure of a set can be uniformly approximated
by a finite subset of that set. Empty compact sets require no exception. -/
theorem exists_finite_subset_thickening_cover
    {E : Type*} [PseudoMetricSpace E] {A S : Set E}
    (hA : IsCompact A) (hAS : A ⊆ closure S) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q : Set E, Q.Finite ∧ Q ⊆ S ∧ A ⊆ thickening δ Q := by
  classical
  have hcover : A ⊆ ⋃ y : S, ball (y : E) δ := by
    intro a ha
    obtain ⟨y, hy, hay⟩ := Metric.mem_closure_iff.mp (hAS ha) δ hδ
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hay⟩
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover
    (fun y : S => ball (y : E) δ) (fun _ => isOpen_ball) hcover
  let Q : Set E := Subtype.val '' (t : Set S)
  refine ⟨Q, t.finite_toSet.image Subtype.val, ?_, ?_⟩
  · rintro y ⟨z, _, rfl⟩
    exact z.property
  · intro a ha
    obtain ⟨y, hyt, hay⟩ := mem_iUnion₂.mp (ht ha)
    exact mem_thickening_iff.mpr ⟨y, ⟨y, hyt, rfl⟩, hay⟩

/-- A finite set outside a compact set approximates its entire boundary.
It has a compact neighbourhood separated from a relatively compact
neighbourhood of the original compact set. These are the two independent
approximation pieces used in the escaping realisation. -/
theorem exists_boundary_barrier_neighborhood
    {E : Type*} [MetricSpace E] [ProperSpace E] {K W : Set E}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (Q R U : Set E),
      Q.Finite ∧ Q ⊆ W \ K ∧ frontier K ⊆ thickening δ Q ∧
      IsCompact R ∧ Q ⊆ interior R ∧ R ⊆ W \ K ∧
      IsOpen U ∧ K ⊆ U ∧ IsCompact (closure U) ∧
      closure U ⊆ W ∧ Disjoint (closure U) R := by
  have hboundary : frontier K ⊆ closure (W \ K) := by
    intro x hx
    apply hW.inter_closure
    exact ⟨hKW (hK.isClosed.frontier_subset hx),
      (frontier_eq_closure_inter_closure (s := K) ▸ hx).2⟩
  have hfrontier : IsCompact (frontier K) :=
    hK.of_isClosed_subset isClosed_frontier hK.isClosed.frontier_subset
  obtain ⟨Q, hQfin, hQsub, hQcover⟩ :=
    exists_finite_subset_thickening_cover hfrontier hboundary hδ
  obtain ⟨V, hV, hQV, hVsub, hVc⟩ :=
    exists_open_between_and_isCompact_closure hQfin.isCompact
      (hW.sdiff hK.isClosed) hQsub
  let R := closure V
  have hKR : Disjoint K R := by
    apply Set.disjoint_left.mpr
    intro z hzK hzR
    exact (hVsub hzR).2 hzK
  have hKWout : K ⊆ W \ R := fun z hz =>
    ⟨hKW hz, fun hr => Set.disjoint_left.mp hKR hz hr⟩
  obtain ⟨U, hU, hKU, hUsub, hUc⟩ :=
    exists_open_between_and_isCompact_closure hK
      (hW.sdiff isClosed_closure) hKWout
  refine ⟨Q, R, U, hQfin, hQsub, hQcover, hVc,
    hQV.trans hV.subset_interior_closure, hVsub, hU, hKU, hUc,
    (fun z hz => (hUsub hz).1), ?_⟩
  exact Set.disjoint_left.mpr (fun z hz hR => (hUsub hz).2 hR)

end FunctionTheory
