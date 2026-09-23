import FunctionTheory.Conformal.BlochUnit

open Set Metric

namespace FunctionTheory

set_option autoImplicit false

/-- The image-disc consequence of Bloch's theorem on an arbitrary disc. -/
theorem exists_bloch_ball_subset_image
    {f : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {r : ℝ}
    (hr : 0<r) (hf : AnalyticOnNhd ℂ f U)
    (hsub : closedBall c r ⊆ U) (hd : deriv f c≠0) :
    ∃ w : ℂ, ball w (r*‖deriv f c‖/256) ⊆ f '' ball c r := by
  let F := fun z : ℂ => f (c+(r:ℂ)*z)
  have hinside : ∀ z∈closedBall (0:ℂ) 1, c+(r:ℂ)*z∈closedBall c r := by
    intro z hz
    rw [mem_closedBall_iff_norm,add_sub_cancel_left,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hr]
    have hz' : ‖z‖≤1 := mem_closedBall_zero_iff.mp hz
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hz' hr.le
  have hF : AnalyticOnNhd ℂ F (closedBall (0:ℂ) 1) := by
    intro z hz
    exact (hf _ (hsub (hinside z hz))).comp
      (f := fun z : ℂ => c+(r:ℂ)*z) (x := z) (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
  have hfc := (hf c (hsub (mem_closedBall_self hr.le))).differentiableAt
  have hfc' : HasDerivAt f (deriv f c) (c+(r:ℂ)*0) := by simpa using hfc.hasDerivAt
  have hFD : deriv F 0=deriv f c*(r:ℂ) := by
    have H := hfc'.comp 0 (((hasDerivAt_id 0).const_mul (r:ℂ)).const_add c)
    simpa only [F,id_eq,mul_one,Function.comp_def] using H.deriv
  have hFD0 : deriv F 0≠0 := by
    rw [hFD]
    exact mul_ne_zero hd (by exact_mod_cast hr.ne')
  obtain ⟨a,s,hs,hasub,hi,hball⟩ := exists_bloch_disc_of_analytic_closedUnitDisc hF hFD0
  have hn : ‖deriv F 0‖=r*‖deriv f c‖ := by
    rw [hFD,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,mul_comm]
  refine ⟨F a,?_⟩
  intro y hy
  rw [← hn] at hy
  obtain ⟨z,hz,hzy⟩ := hball hy
  refine ⟨c+(r:ℂ)*z,?_,hzy⟩
  rw [mem_ball_iff_norm,add_sub_cancel_left,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hr]
  have hz' : ‖z‖<1 := mem_ball_zero_iff.mp (hasub hz)
  simpa only [mul_one] using mul_lt_mul_of_pos_left hz' hr

/-- Omitting a point from every target disc of a fixed radius bounds the
derivative. This is the Bloch input to the Schottky estimate. -/
theorem norm_deriv_le_of_no_image_ball
    {f : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {r M : ℝ}
    (hr : 0<r) (hM : 0≤M) (hf : AnalyticOnNhd ℂ f U)
    (hsub : closedBall c r ⊆ U)
    (hno : ∀ w : ℂ, ¬ ball w M ⊆ f '' U) :
    ‖deriv f c‖≤256*M/r := by
  by_cases hd : deriv f c=0
  · rw [hd,norm_zero]
    positivity
  · obtain ⟨w,hw⟩ := exists_bloch_ball_subset_image hr hf hsub hd
    by_contra hn
    have H : 256*M<‖deriv f c‖*r := (div_lt_iff₀ hr).mp (lt_of_not_ge hn)
    have hrad : M≤r*‖deriv f c‖/256 := by nlinarith
    exact hno w ((ball_subset_ball hrad).trans
      (hw.trans (image_mono (ball_subset_closedBall.trans hsub))))

end FunctionTheory
