/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.EntireFatouBridge
import EremenkosConjecture.FilledDomainComponents
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

/-- Reuse the supplied Schoenflies-based planar theorem for the trapped set. -/
theorem trapped_closed_disc_component_simplyConnected {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {R : ℝ} {z : ℂ}
    (hz : z ∈ interior (trappedSet f (closedBall 0 R))) :
    IsSimplyConnected (connectedComponentIn (interior (trappedSet f (closedBall 0 R))) z) :=
  EremenkosConjecture.isSimplyConnected_component_interior_of_noBoundedComplementComponents
    (trapped_closed_disc_no_bounded_complement hf R) hz

/-- A uniformly bounded orbit of genuine Fatou components is simply connected.
This is a consequence, not an extra orbit hypothesis. -/
theorem bounded_fatou_orbit_simplyConnected {f : ℂ → ℂ} {U : ℕ → Set ℂ}
    (hf : Differentiable ℂ f) (hn : ∀ x, ¬Filter.EventuallyConst f (nhds x))
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hforward : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hbounded : Bornology.IsBounded (⋃ n, U n)) {z : ℂ} (hz : z ∈ U 0) :
    ∀ n, IsSimplyConnected (U n) := by
  obtain ⟨R, _, hbound⟩ := hbounded.exists_pos_norm_le
  have hUV : ∀ n, U n ⊆ closedBall 0 R := by
    intro n w hw
    exact mem_closedBall_zero_iff.mpr (hbound w (mem_iUnion.mpr ⟨n, hw⟩))
  obtain ⟨hzT, hUT⟩ := fatou_orbit_eq_trapped_components hf hn isBounded_closedBall
    hU hforward hUV hz
  intro n
  rw [hUT n]
  exact trapped_closed_disc_component_simplyConnected hf (hzT n)

end AreaDeficit

#print axioms AreaDeficit.trapped_closed_disc_no_bounded_complement
#print axioms AreaDeficit.bounded_fatou_orbit_simplyConnected
