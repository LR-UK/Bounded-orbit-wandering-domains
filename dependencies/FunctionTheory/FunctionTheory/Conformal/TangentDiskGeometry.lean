import FunctionTheory.Conformal.BoundaryPointExtension
import TauCeti.Topology.JordanCurve.Basic
import Mathlib.Analysis.InnerProductSpace.Convex

open Set Metric Complex

namespace FunctionTheory

/-- An internally tangent closed disk touches the unit circle only at its
specified tangency point. All other points lie in the open unit disk. -/
theorem tangent_closedBall_subset_insert_ball {ξ : ℂ} {t : ℝ}
    (hξ : ‖ξ‖ = 1) (ht : 0 < t) (ht1 : t < 1) :
    closedBall ((t : ℂ) * ξ) (1 - t) ⊆ insert ξ (ball (0 : ℂ) 1) := by
  intro z hz
  by_cases hzξ : z = ξ
  · exact Or.inl hzξ
  · right
    let w : ℂ := (z - (t : ℂ) * ξ) / ((1 - t : ℝ) : ℂ)
    have hr : 0 < 1 - t := sub_pos.mpr ht1
    have hr0 : ((1 - t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hw : ‖w‖ ≤ 1 := by
      dsimp only [w]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      exact (div_le_one hr).mpr (by simpa only [mem_closedBall, dist_eq_norm] using hz)
    have heq : (t : ℝ) • ξ + (1 - t) • w = z := by
      simp only [Complex.real_smul, w]
      rw [mul_div_cancel₀ _ hr0]
      ring
    have hne : ξ ≠ w := by
      intro he
      apply hzξ
      rw [← he] at heq
      simpa only [← add_smul, add_sub_cancel, one_smul] using heq.symm
    have h := combo_mem_ball_of_ne
      (show ξ ∈ closedBall (0 : ℂ) 1 by simpa [mem_closedBall, hξ])
      (show w ∈ closedBall (0 : ℂ) 1 by simpa [mem_closedBall] using hw)
      hne ht hr (by ring : t + (1 - t) = 1)
    rwa [heq] at h

theorem tangency_point_mem_sphere {ξ : ℂ} {t : ℝ}
    (hξ : ‖ξ‖ = 1) (ht1 : t < 1) : ξ ∈ sphere ((t : ℂ) * ξ) (1 - t) := by
  rw [mem_sphere, dist_eq_norm]
  have he : ξ - (t : ℂ) * ξ = ((1 - t : ℝ) : ℂ) * ξ := by push_cast; ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht1), hξ, mul_one]

theorem zero_mem_tangent_ball {ξ : ℂ} {t : ℝ}
    (hξ : ‖ξ‖ = 1) (ht : 0 < t) (htHalf : t < 1 / 2) :
    (0 : ℂ) ∈ ball ((t : ℂ) * ξ) (1 - t) := by
  rw [mem_ball, dist_zero_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ht, hξ, mul_one]
  linarith

/-- A continuous injection on the disk with one boundary point adjoined
carries an internally tangent circle to a Jordan curve through that value. -/
theorem isJordanCurve_image_tangent_sphere
    {G : ℂ → ℂ} {ξ : ℂ} {t : ℝ}
    (hξ : ‖ξ‖ = 1) (ht : 0 < t) (ht1 : t < 1)
    (hGc : ContinuousOn G (insert ξ (ball (0 : ℂ) 1)))
    (hGi : InjOn G (insert ξ (ball (0 : ℂ) 1))) :
    TauCeti.IsJordanCurve (G '' sphere ((t : ℂ) * ξ) (1 - t)) ∧
      G ξ ∈ G '' sphere ((t : ℂ) * ξ) (1 - t) := by
  have hsub := sphere_subset_closedBall.trans (tangent_closedBall_subset_insert_ball hξ ht ht1)
  exact ⟨(TauCeti.isJordanCurve_sphere _ (sub_pos.mpr ht1)).image (hGc.mono hsub) (hGi.mono hsub),
    mem_image_of_mem _ (tangency_point_mem_sphere hξ ht1)⟩

end FunctionTheory
