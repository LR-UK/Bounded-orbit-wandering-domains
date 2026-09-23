import FunctionTheory.Conformal.LocalCircularBoundary

open Set Metric Complex Filter
open scoped Topology

namespace FunctionTheory

theorem circleMap_mem_slitPlane_of_angle
    {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : θ ∈ Ioo (-Real.pi) Real.pi) :
    circleMap (0 : ℂ) ρ θ ∈ slitPlane := by
  apply mem_slitPlane_iff_arg.mpr
  refine ⟨?_, circleMap_ne_center hρ.ne'⟩
  rw [circleMap_zero, arg_real_mul _ hρ, arg_exp_mul_I,
    (toIocMod_eq_self Real.two_pi_pos).mpr
      ⟨hθ.1, by linarith [hθ.2]⟩]
  exact hθ.2.ne

/-- Circular crosscuts at the free endpoint of a straight slit. -/
theorem circular_approach_of_local_slit
    {U : Set ℂ} {R : ℝ} (hR : 0 < R)
    (hlocal : U ∩ ball (0 : ℂ) R = slitPlane ∩ ball 0 R) :
    (0 : ℂ) ∈ frontier U ∧
    ∀ ρ ∈ Ioo 0 R,
      (∀ θ ∈ Ioo (-Real.pi) Real.pi, circleMap 0 ρ θ ∈ U) ∧
      circleMap 0 ρ Real.pi ∈ frontier U ∧
      ∀ z ∈ U ∩ sphere (0 : ℂ) ρ,
        ∃ θ ∈ Ioo (-Real.pi) Real.pi, z = circleMap 0 ρ θ := by
  have hmem : ∀ z ∈ ball (0 : ℂ) R, z ∈ U ↔ z ∈ slitPlane := by
    intro z hz
    have h := congrArg (fun S : Set ℂ => z ∈ S) hlocal
    simpa only [mem_inter_iff, hz, and_true] using iff_of_eq h
  have harc : ∀ ρ ∈ Ioo 0 R, ∀ θ ∈ Ioo (-Real.pi) Real.pi,
      circleMap 0 ρ θ ∈ U := by
    intro ρ hρ θ hθ
    apply (hmem _ ?_).mpr (circleMap_mem_slitPlane_of_angle hρ.1 hθ)
    simpa only [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos hρ.1] using hρ.2
  have h0cl : (0 : ℂ) ∈ closure U := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let ρ := min R ε / 2
    have hρ : 0 < ρ := half_pos (lt_min hR hε)
    have hρR : ρ < R := (half_lt_self (lt_min hR hε)).trans_le (min_le_left _ _)
    have hρε : ρ < ε := (half_lt_self (lt_min hR hε)).trans_le (min_le_right _ _)
    refine ⟨circleMap 0 ρ 0, harc ρ ⟨hρ, hρR⟩ 0
      ⟨neg_neg_of_pos Real.pi_pos, Real.pi_pos⟩, ?_⟩
    simpa [dist_comm, dist_zero_right, norm_circleMap_zero, abs_of_pos hρ] using hρε
  have h0not : (0 : ℂ) ∉ U := by
    intro h
    exact zero_notMem_slitPlane ((hmem 0 (by simpa using hR)).mp h)
  refine ⟨⟨h0cl, fun h => h0not (interior_subset h)⟩, ?_⟩
  intro ρ hρ
  refine ⟨harc ρ hρ, ?_, ?_⟩
  · have hc : Continuous (circleMap (0 : ℂ) ρ) := by unfold circleMap; fun_prop
    have hcl : circleMap 0 ρ Real.pi ∈ closure
        (circleMap (0 : ℂ) ρ '' Ioo (-Real.pi) Real.pi) := by
      apply hc.continuousAt.continuousWithinAt.mem_closure_image
      rw [closure_Ioo (by linarith [Real.pi_pos] : -Real.pi ≠ Real.pi)]
      exact ⟨by linarith [Real.pi_pos], le_rfl⟩
    refine ⟨closure_mono (by rintro _ ⟨θ, hθ, rfl⟩; exact harc ρ hρ θ hθ) hcl, ?_⟩
    intro hint
    have hU := interior_subset hint
    have hslit := (hmem _ (by
      simpa only [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos hρ.1]
        using hρ.2)).mp hU
    have heq : circleMap (0 : ℂ) ρ Real.pi = -(ρ : ℂ) := by
      simp [circleMap, exp_pi_mul_I]
    rw [heq, neg_ofReal_mem_slitPlane] at hslit
    linarith [hρ.1]
  · intro z hz
    have hnorm : ‖z‖ = ρ := by simpa only [mem_sphere, dist_zero_right] using hz.2
    have hzs : z ∈ slitPlane := (hmem z (by
      simpa only [mem_ball, dist_zero_right, hnorm] using hρ.2)).mp hz.1
    refine ⟨z.arg, ⟨neg_pi_lt_arg z, (arg_le_pi z).lt_of_ne (slitPlane_arg_ne_pi hzs)⟩, ?_⟩
    simpa only [circleMap_zero, ← hnorm] using (norm_mul_exp_arg_mul_I z).symm

/-- A conformal disk map has a unique boundary value at a free straight-slit
endpoint. No hypothesis is made on the domain boundary away from this point. -/
theorem exists_boundary_limit_at_slit_tip
    {U : Set ℂ} {f : ℂ → ℂ} {R : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (hR : 0 < R) (hlocal : U ∩ ball (0 : ℂ) R = slitPlane ∩ ball 0 R) :
    ∃ a ∈ sphere (0 : ℂ) 1, Tendsto f (𝓝[U] 0) (𝓝 a) := by
  obtain ⟨h0, harcs⟩ := circular_approach_of_local_slit hR hlocal
  exact exists_boundary_limit_of_circular_approach hU hf hbij h0 hR
    (neg_neg_of_pos Real.pi_pos) Real.pi_pos (by linarith) harcs

end FunctionTheory
