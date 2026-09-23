import FunctionTheory.Conformal.SlitTipInverseCoordinates
import FunctionTheory.Conformal.TangentDiskGeometry

open Set Metric Complex Filter Function
open scoped Topology

namespace FunctionTheory

/-- Inverse continuity at a free slit tip supplies Jordan curves through the
tip whose other points lie in the original domain. This does not yet assert
which complementary set the curves surround. -/
theorem exists_jordan_curves_through_reflected_slit_tip
    {U : Set ℂ} {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (hR : 0 < R)
    (hlocal : {z : ℂ | c - z ∈ U} ∩ ball (0 : ℂ) R = slitPlane ∩ ball 0 R) :
    ∃ (ξ : ℂ) (G : ℂ → ℂ), ξ ∈ sphere (0 : ℂ) 1 ∧
      ContinuousOn G (insert ξ (ball (0 : ℂ) 1)) ∧
      InjOn G (insert ξ (ball (0 : ℂ) 1)) ∧
      EqOn G (invFunOn f U) (ball 0 1) ∧ G ξ = c ∧
      ∀ t : ℝ, 0 < t → t < 1 →
        TauCeti.IsJordanCurve (G '' sphere ((t : ℂ) * ξ) (1 - t)) ∧
        c ∈ G '' sphere ((t : ℂ) * ξ) (1 - t) ∧
        (G '' sphere ((t : ℂ) * ξ) (1 - t)) \ {c} ⊆ U := by
  obtain ⟨ξ, hξ, hg⟩ := exists_inverse_boundary_limit_at_reflected_slit_tip hU hf hbij hR hlocal
  have hξnorm : ‖ξ‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hξ
  have hξD : ξ ∉ ball (0 : ℂ) 1 := by simp [mem_ball, hξnorm]
  have hcU : c ∉ U := by
    intro hc
    have h : (0 : ℂ) ∈ {z : ℂ | c - z ∈ U} ∩ ball (0 : ℂ) R :=
      ⟨by simpa using hc, mem_ball_self hR⟩
    rw [hlocal] at h
    simpa using h.1
  have hgd : DifferentiableOn ℂ (invFunOn f U) (ball 0 1) := by
    simpa only [hbij.image_eq] using hf.invFunOn hU hbij.injOn
  have hgi : InjOn (invFunOn f U) (ball 0 1) := by
    intro z hz w hw he
    have he' := congrArg f he
    simpa only [hbij.surjOn.rightInvOn_invFunOn hz, hbij.surjOn.rightInvOn_invFunOn hw] using he'
  have hcrange : c ∉ invFunOn f U '' ball (0 : ℂ) 1 := by
    rintro ⟨z, hz, rfl⟩
    exact hcU (hbij.surjOn.mapsTo_invFunOn hz)
  obtain ⟨G, hGc, hGi, heq, hGξ⟩ := exists_continuous_injective_extension_at_boundary_point
    hgd.continuousOn hgi hξD hcrange hg
  refine ⟨ξ, G, hξ, hGc, hGi, heq, hGξ, ?_⟩
  intro t ht ht1
  obtain ⟨hcurve, htip⟩ := isJordanCurve_image_tangent_sphere hξnorm ht ht1 hGc hGi
  refine ⟨hcurve, by rwa [hGξ] at htip, ?_⟩
  rintro z ⟨⟨w, hw, rfl⟩, hzc⟩
  have hw' := tangent_closedBall_subset_insert_ball hξnorm ht ht1 (sphere_subset_closedBall hw)
  rcases hw' with rfl | hwD
  · exact (hzc (by simp [hGξ])).elim
  · rw [heq hwD]
    exact hbij.surjOn.mapsTo_invFunOn hwD

/-- Tangent circles with their centre less than halfway to the boundary
surround the disk origin in the parameter plane, so their injective images
avoid the image of the origin. -/
theorem image_zero_notMem_image_tangent_sphere
    {G : ℂ → ℂ} {ξ : ℂ} {t : ℝ}
    (hξ : ‖ξ‖ = 1) (ht : 0 < t) (htHalf : t < 1 / 2)
    (hGi : InjOn G (insert ξ (ball (0 : ℂ) 1))) :
    G 0 ∉ G '' sphere ((t : ℂ) * ξ) (1 - t) := by
  rintro ⟨z, hz, he⟩
  have ht1 : t < 1 := by linarith
  have hzD := tangent_closedBall_subset_insert_ball hξ ht ht1 (sphere_subset_closedBall hz)
  have hz0 : z = 0 := hGi hzD (Or.inr (mem_ball_self zero_lt_one)) he
  subst z
  have hb := zero_mem_tangent_ball hξ ht htHalf
  exact (lt_irrefl _) ((mem_ball.mp hb).trans_le (mem_sphere.mp hz).ge)

end FunctionTheory
