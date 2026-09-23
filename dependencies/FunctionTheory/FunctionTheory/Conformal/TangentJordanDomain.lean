import FunctionTheory.Conformal.TangentDiskGeometry
import TauCeti.Analysis.Complex.Conformal.BoundaryCorrespondence

open Set Metric Complex

namespace FunctionTheory

theorem tangent_ball_subset_unitDisk {ξ : ℂ} {t : ℝ}
    (hξ : ‖ξ‖ = 1) (ht : 0 < t) :
    ball ((t : ℂ) * ξ) (1 - t) ⊆ ball (0 : ℂ) 1 := by
  intro z hz
  have hc : dist ((t : ℂ) * ξ) 0 = t := by
    simp [dist_zero_right, norm_mul, hξ, abs_of_pos ht]
  have htri := dist_triangle z ((t : ℂ) * ξ) 0
  rw [hc] at htri
  rw [mem_ball] at hz ⊢
  linarith

/-- A univalent disk map continuous at one circle point maps an internally
tangent disk to a bounded Jordan domain. Its boundary is exactly the image
of the tangent circle. -/
theorem tangent_disk_image_is_bounded_jordan_domain
    {G : ℂ → ℂ} {ξ : ℂ} {t : ℝ}
    (hξ : ‖ξ‖ = 1) (ht : 0 < t) (ht1 : t < 1)
    (hGc : ContinuousOn G (insert ξ (ball (0 : ℂ) 1)))
    (hGi : InjOn G (insert ξ (ball (0 : ℂ) 1)))
    (hGd : DifferentiableOn ℂ G (ball 0 1)) :
    IsOpen (G '' ball ((t : ℂ) * ξ) (1 - t)) ∧
      IsConnected (G '' ball ((t : ℂ) * ξ) (1 - t)) ∧
      Bornology.IsBounded (G '' ball ((t : ℂ) * ξ) (1 - t)) ∧
      frontier (G '' ball ((t : ℂ) * ξ) (1 - t)) =
        G '' sphere ((t : ℂ) * ξ) (1 - t) ∧
      TauCeti.IsJordanCurve (frontier (G '' ball ((t : ℂ) * ξ) (1 - t))) := by
  have hr : 0 < 1 - t := sub_pos.mpr ht1
  have hb := tangent_ball_subset_unitDisk hξ ht
  have hcb := tangent_closedBall_subset_insert_ball hξ ht ht1
  have hb' := hb.trans (subset_insert ξ (ball (0 : ℂ) 1))
  have hd := hGd.mono hb
  have hi := hGi.mono hb'
  have hcl : ContinuousOn G (closure (ball ((t : ℂ) * ξ) (1 - t))) := by
    rw [closure_ball _ hr.ne']
    exact hGc.mono hcb
  have hfr : frontier (G '' ball ((t : ℂ) * ξ) (1 - t)) =
      G '' sphere ((t : ℂ) * ξ) (1 - t) := by
    rw [← TauCeti.image_frontier_eq_frontier_image isOpen_ball isBounded_ball hd hi hcl
      (fun _ _ => rfl), frontier_ball _ hr.ne']
  refine ⟨TauCeti.isOpen_image_of_differentiableOn_of_injOn isOpen_ball hd hi,
    (convex_ball _ _).isConnected (nonempty_ball.mpr hr) |>.image G hd.continuousOn,
    ?_, hfr, ?_⟩
  · exact ((isCompact_closedBall _ _).image_of_continuousOn (hGc.mono hcb)).isBounded.subset
      (image_mono ball_subset_closedBall)
  · rw [hfr]
    exact (isJordanCurve_image_tangent_sphere hξ ht ht1 hGc hGi).1

end FunctionTheory
