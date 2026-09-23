import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

open Set Metric

namespace FunctionTheory

set_option autoImplicit false

/-- Every plane disc contains two smaller discs with disjoint closures,
both with a strict margin inside the original disc. -/
theorem exists_two_disjoint_closed_subdiscs (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ (a b : ℂ) (s : ℝ), 0 < s ∧
      closedBall a s ⊆ ball c r ∧ closedBall b s ⊆ ball c r ∧
      Disjoint (closedBall a s) (closedBall b s) := by
  let t : ℝ := r/2
  have ht : 0 < t := half_pos hr
  have hnorm : ‖(t : ℂ)‖ = t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hplus : dist (c+(t : ℂ)) c = t := by
    rw [dist_eq_norm, add_sub_cancel_left, hnorm]
  have hminus : dist (c-(t : ℂ)) c = t := by
    rw [dist_eq_norm, show c-(t : ℂ)-c = -(t : ℂ) by ring, norm_neg, hnorm]
  have hbetween : dist (c+(t : ℂ)) (c-(t : ℂ)) = r := by
    rw [dist_eq_norm]
    have heq : c+(t : ℂ)-(c-(t : ℂ)) = (r : ℂ) := by
      dsimp [t]
      push_cast
      ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  refine ⟨c+(t : ℂ),c-(t : ℂ),r/4,by positivity,?_,?_,?_⟩
  · apply closedBall_subset_ball'
    rw [hplus]
    dsimp [t]
    linarith
  · apply closedBall_subset_ball'
    rw [hminus]
    dsimp [t]
    linarith
  · apply closedBall_disjoint_closedBall
    rw [hbetween]
    linarith

end FunctionTheory
