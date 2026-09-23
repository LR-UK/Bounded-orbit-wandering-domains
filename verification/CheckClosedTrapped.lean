/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.EntireFatouBridge
import ComplexApproximation.Topology.Filling
import ComplexApproximation.Topology.Nonseparation
import Mathlib.Analysis.Complex.AbsMax

open Set Metric Function

namespace AreaDeficit

/-- The points whose entire orbit stays in a closed disc form a closed set. -/
theorem isClosed_trapped_closed_disc {f : ℂ → ℂ} (hf : Continuous f) (R : ℝ) :
    IsClosed (trappedSet f (closedBall 0 R)) := by
  have he : trappedSet f (closedBall 0 R) =
      ⋂ n : ℕ, (f^[n]) ⁻¹' closedBall 0 R := by
    ext z
    simp [trappedSet]
  rw [he]
  exact isClosed_iInter (fun n => isClosed_closedBall.preimage (hf.iterate n))

/-- Maximum modulus rules out every bounded complementary component of
the closed-disc trapped set. No simple-connectivity assumption is used. -/
theorem trapped_closed_disc_no_bounded_complement {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (R : ℝ) :
    ComplexApproximation.NoBoundedComplementComponents (trappedSet f (closedBall 0 R)) := by
  intro z hz hb
  let F := trappedSet f (closedBall 0 R)
  let D := connectedComponentIn Fᶜ z
  have hF : IsClosed F := isClosed_trapped_closed_disc hf.continuous R
  have hfront : frontier D ⊆ F := by
    simpa only [compl_compl] using
      ComplexApproximation.frontier_component_subset_compl hF.isOpen_compl hz
  have hzD : z ∈ D := mem_connectedComponentIn hz
  apply hz
  intro n
  apply mem_closedBall_zero_iff.mpr
  apply Complex.norm_le_of_forall_mem_frontier_norm_le hb (hf.iterate n).diffContOnCl
    (fun w hw => mem_closedBall_zero_iff.mp (hfront hw n)) (subset_closure hzD)


end AreaDeficit
