import FunctionTheory.Conformal.AffineReturnChannel
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Compact

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Small perturbations of an expanding affine map do not contract between
any channel preimages of a fixed compact target. This controls every such
preimage, rather than only those already known to lie on a selected branch. -/
theorem exists_affine_target_noncontraction_tolerance
    {K : Set ℂ} (hK : IsCompact K) (c a : ℂ) {r : ℝ} (hr : 0 < r)
    (ha : 2 ≤ ‖a‖)
    (hcover : K ⊆ (fun z => a*(z-c)) '' ball c r) :
    ∃ δ > 0, ∀ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f (closedBall c r) →
      (∀ z ∈ closedBall c r, dist (f z) (a*(z-c)) ≤ δ) →
      (∀ z ∈ closedBall c r, f z ∈ K → 1 ≤ ‖deriv f z‖) ∧
      ∀ x ∈ closedBall c r, f x ∈ K →
        ∀ y ∈ closedBall c r, f y ∈ K → dist x y ≤ dist (f x) (f y) := by
  by_cases hne : K.Nonempty
  · obtain ⟨w,hw,hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
    have hap : 0 < ‖a‖ := by linarith
    have hwr : ‖w‖ < ‖a‖*r := by
      obtain ⟨u,hu,rfl⟩ := hcover hw
      rw [norm_mul]
      exact mul_lt_mul_of_pos_left (by simpa only [mem_ball,dist_eq_norm] using hu) hap
    have hdiv : ‖w‖/‖a‖ < r := (div_lt_iff₀ hap).mpr (by nlinarith)
    obtain ⟨s,hws,hsr⟩ := exists_between hdiv
    have hsp : 0 < s := (div_nonneg (norm_nonneg w) hap.le).trans_lt hws
    have hgap : 0 < ‖a‖*s-‖w‖ := by
      have H := (div_lt_iff₀ hap).mp hws
      nlinarith
    obtain ⟨d,hd,Hderiv⟩ := exists_derivative_approximation_tolerance
      (ball c r) (closedBall c s) isOpen_ball (isCompact_closedBall _ _)
      (closedBall_subset_ball hsr) 1 (by norm_num)
    let δ : ℝ := min d ((‖a‖*s-‖w‖)/2)
    have hδ : 0 < δ := lt_min hd (half_pos hgap)
    refine ⟨δ,hδ,?_⟩
    intro f hf hclose
    let φ : ℂ → ℂ := fun z => a*(z-c)
    have hφ : AnalyticOnNhd ℂ φ univ :=
      analyticOnNhd_const.mul (analyticOnNhd_id.sub analyticOnNhd_const)
    have hsub : closedBall c s ⊆ closedBall c r :=
      closedBall_subset_closedBall hsr.le
    have hinside : ∀ z ∈ closedBall c r, f z ∈ K → z ∈ ball c s := by
      intro z hz hk
      have hnorm : ‖a‖*‖z-c‖ ≤ ‖w‖+δ := by
        calc
          ‖a‖*‖z-c‖ = ‖a*(z-c)‖ := (norm_mul _ _).symm
          _ ≤ ‖f z‖+‖f z-a*(z-c)‖ := by
            have H := norm_sub_le (f z) (f z-a*(z-c))
            simpa only [sub_sub_cancel] using H
          _ ≤ ‖w‖+δ := add_le_add (hmax hk)
            (by simpa only [dist_eq_norm] using hclose z hz)
      have hsmall : δ ≤ (‖a‖*s-‖w‖)/2 := min_le_right _ _
      rw [mem_ball,dist_eq_norm]
      by_contra hn
      have H := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hap.le
      nlinarith
    have hdφ : ∀ z, deriv φ z=a := by
      intro z
      have H := ((hasDerivAt_id z).sub_const c).const_mul a
      simpa only [φ,id_eq,mul_one] using H.deriv
    have hderiv : ∀ z ∈ closedBall c s, ‖deriv f z-a‖ < 1 := by
      intro z hz
      have H := Hderiv f φ
        ((hf.mono ball_subset_closedBall).differentiableOn)
        (hφ.differentiableOn.mono (subset_univ _))
        (fun v hv => (hclose v (ball_subset_closedBall hv)).trans (min_le_left _ _)) z hz
      rwa [hdφ z] at H
    refine ⟨?_,?_⟩
    · intro z hz hk
      have H := hderiv z (ball_subset_closedBall (hinside z hz hk))
      have Hnorm := norm_sub_norm_le a (deriv f z)
      rw [norm_sub_rev] at Hnorm
      linarith
    · intro x hx hxK y hy hyK
      have hx' := ball_subset_closedBall (hinside x hx hxK)
      have hy' := ball_subset_closedBall (hinside y hy hyK)
      let e : ℂ → ℂ := fun z => f z-φ z
      have heD : ∀ z ∈ closedBall c s, DifferentiableAt ℂ e z := fun z hz =>
        ((hf z (hsub hz)).sub (hφ z (mem_univ z))).differentiableAt
      have hederiv : ∀ z ∈ closedBall c s, ‖deriv e z‖ ≤ 1 := by
        intro z hz
        have heq : deriv e z=deriv f z-deriv φ z :=
          ((hf z (hsub hz)).differentiableAt.hasDerivAt.sub
            (hφ z (mem_univ z)).differentiableAt.hasDerivAt).deriv
        rw [heq,hdφ z]
        exact (hderiv z hz).le
      have hLip := (convex_closedBall c s).norm_image_sub_le_of_norm_deriv_le
        heD hederiv hy' hx'
      simp only [one_mul] at hLip
      have htri : ‖a‖*‖x-y‖ ≤ ‖f x-f y‖+‖e x-e y‖ := by
        calc
          ‖a‖*‖x-y‖ = ‖(f x-f y)-(e x-e y)‖ := by
            rw [← norm_mul]
            congr 1
            dsimp only [e,φ]
            ring
          _ ≤ _ := norm_sub_le _ _
      rw [dist_eq_norm,dist_eq_norm]
      have H := mul_le_mul_of_nonneg_right ha (norm_nonneg (x-y))
      nlinarith
  · refine ⟨1,by norm_num,?_⟩
    intro f hf hclose
    exact ⟨fun z hz hk => (hne ⟨f z,hk⟩).elim,
      fun x hx hxK y hy hyK => (hne ⟨f x,hxK⟩).elim⟩

end FunctionTheory
