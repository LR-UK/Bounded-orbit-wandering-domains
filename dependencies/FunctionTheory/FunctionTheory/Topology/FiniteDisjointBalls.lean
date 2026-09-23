import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

open Set Metric

namespace FunctionTheory

set_option autoImplicit false

/-- Finitely many distinct points admit pairwise disjoint closed balls of
a common positive radius, including the empty and singleton cases. -/
theorem exists_pairwise_disjoint_closedBalls_of_finite
    {X : Type*} [MetricSpace X] {C : Set X} (hC : C.Finite) :
    ∃ r > 0, ∀ a ∈ C, ∀ b ∈ C, a ≠ b → Disjoint (closedBall a r) (closedBall b r) := by
  let S : Set (X × X) := {p | p.1 ∈ C ∧ p.2 ∈ C ∧ p.1 ≠ p.2}
  have hS : S.Finite := (hC.prod hC).subset (fun p hp => ⟨hp.1, hp.2.1⟩)
  obtain ⟨d, hd, H⟩ := hS.isCompact.exists_forall_le'
    (continuous_fst.dist continuous_snd).continuousOn (fun p hp => dist_pos.mpr hp.2.2)
  refine ⟨d / 4, by positivity, ?_⟩
  intro a ha b hb hab
  apply Set.disjoint_left.mpr
  intro z hza hzb
  have haz : dist a z ≤ d / 4 := by simpa only [dist_comm] using mem_closedBall.mp hza
  have hzb' : dist z b ≤ d / 4 := mem_closedBall.mp hzb
  have hsep := H (a, b) ⟨ha, hb, hab⟩
  linarith [dist_triangle a z b]

end FunctionTheory
