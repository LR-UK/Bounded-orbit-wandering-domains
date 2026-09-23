import BoundedWanderingDomains.LocalTrappedTopology
import Mathlib.Analysis.Complex.AbsMax

open Set Metric Function

namespace AreaDeficit

/-- Maximum modulus fills every bounded open region whose boundary is
trapped in a fixed disc. This is the analytic step towards simple connectivity. -/
theorem bounded_region_subset_trapped_interior {f : ℂ → ℂ} {D : Set ℂ} {R : ℝ}
    (hf : Differentiable ℂ f) (hD : IsOpen D) (hb : Bornology.IsBounded D)
    (hfront : frontier D ⊆ trappedSet f (ball 0 R)) :
    D ⊆ interior (trappedSet f (ball 0 R)) := by
  apply hD.subset_interior_iff.mpr
  intro z hz n
  have hd : Differentiable ℂ (f^[n]) := hf.iterate n
  obtain ⟨w, hw, hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm hb ⟨z, hz⟩
    hd.diffContOnCl
  exact mem_ball_zero_iff.mpr ((hmax (subset_closure hz)).trans_lt
    (mem_ball_zero_iff.mp (hfront hw n)))

end AreaDeficit

#print axioms AreaDeficit.bounded_region_subset_trapped_interior
