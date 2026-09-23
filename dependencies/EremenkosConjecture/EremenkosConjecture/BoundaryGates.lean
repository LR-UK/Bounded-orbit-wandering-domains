import EremenkosConjecture.PlaneTopology

/-! # Removing a small opening from a surrounding boundary -/

open Set Metric

namespace EremenkosConjecture

/-- If both sides of a compact boundary are connected and the compact set is
the closure of its interior, removing a ball about a boundary point leaves
a compact nonseparating set. No smoothness or parametrisation is needed. -/
theorem boundary_sdiff_ball_isCompact_isFull {L : Set ℂ}
    (hL : IsCompact L) (hi : IsConnected (interior L)) (ho : IsConnected Lᶜ)
    (hreg : L = closure (interior L)) {a : ℂ} (ha : a ∈ frontier L)
    {r : ℝ} (hr : 0 < r) :
    IsCompact (frontier L \ ball a r) ∧ IsConnected (frontier L \ ball a r)ᶜ := by
  refine ⟨(hL.of_isClosed_subset isClosed_frontier
    (frontier_subset_closure.trans hL.isClosed.closure_eq.subset)).diff isOpen_ball, ?_⟩
  have haL : a ∈ L := hL.isClosed.closure_eq ▸ ha.1
  have hac : a ∈ closure (interior L) := hreg ▸ haL
  obtain ⟨x, hxi, hxa⟩ := Metric.mem_closure_iff.mp hac r hr
  have hxb : x ∈ ball a r := by simpa only [mem_ball, dist_comm] using hxa
  have hao : a ∈ closure Lᶜ := by
    rw [frontier_eq_closure_inter_closure] at ha
    exact ha.2
  obtain ⟨y, hyo, hya⟩ := Metric.mem_closure_iff.mp hao r hr
  have hyb : y ∈ ball a r := by simpa only [mem_ball, dist_comm] using hya
  have hb : IsConnected (ball a r) := (convex_ball a r : Convex ℝ _).isConnected
    ⟨a, mem_ball_self hr⟩
  have hconn := (hi.union ⟨x, hxi, hxb⟩ hb).union ⟨y, Or.inr hyb, hyo⟩ ho
  have heq : (frontier L \ ball a r)ᶜ = (interior L ∪ ball a r) ∪ Lᶜ := by
    rw [frontier, hL.isClosed.closure_eq]
    ext z
    simp only [mem_compl_iff, mem_diff, mem_union]
    tauto
  rwa [heq]

end EremenkosConjecture
