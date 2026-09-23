import FunctionTheory.Conformal.BlochDerivativeBound
import FunctionTheory.Conformal.NormalizedCosineLift
import FunctionTheory.Conformal.SchottkyGrid
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Connected

open Set Metric
namespace FunctionTheory
set_option autoImplicit false

/-- A simple exponential majorant for complex cosine. -/
theorem norm_cos_le_exp_norm (z : ℂ) : ‖Complex.cos z‖≤Real.exp ‖z‖ := by
  have h1 : ‖Complex.exp (z*Complex.I)‖≤Real.exp ‖z‖ := by
    simpa only [norm_mul,Complex.norm_I,mul_one] using Complex.norm_exp_le_exp_norm (z*Complex.I)
  have h2 : ‖Complex.exp (-z*Complex.I)‖≤Real.exp ‖z‖ := by
    simpa only [norm_mul,Complex.norm_I,mul_one,norm_neg] using Complex.norm_exp_le_exp_norm (-z*Complex.I)
  rw [Complex.cos,norm_div]
  rw [show ‖(2:ℂ)‖=(2:ℝ) by norm_num]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  exact (norm_add_le _ _).trans (by linarith)

/-- The derivative consequence of Bloch controls the change of a function
on a smaller disc if its image contains no disc of radius M. -/
theorem norm_sub_le_of_no_image_ball {g : ℂ → ℂ} {M t : ℝ}
    (hM : 0≤M) (ht : 0≤t) (ht1 : t<1)
    (hg : AnalyticOnNhd ℂ g (ball (0:ℂ) 1))
    (hno : ∀ b : ℂ, ¬ ball b M ⊆ g '' ball (0:ℂ) 1)
    {z : ℂ} (hz : ‖z‖≤t) :
    ‖g z-g 0‖≤512*M*t/(1-t) := by
  have hr : 0<(1-t)/2 := by linarith
  have hd : ∀ w∈closedBall (0:ℂ) t, ‖deriv g w‖≤512*M/(1-t) := by
    intro w hw
    have hw' := mem_closedBall_zero_iff.mp hw
    have hsub : closedBall w ((1-t)/2) ⊆ ball (0:ℂ) 1 := by
      intro x hx
      rw [mem_ball_zero_iff]
      have H := mem_closedBall_iff_norm.mp hx
      have H' : ‖x‖≤‖x-w‖+‖w‖ := by
        simpa only [sub_add_cancel] using norm_add_le (x-w) w
      linarith
    have H := norm_deriv_le_of_no_image_ball hr hM hg hsub hno
    convert H using 1
    field_simp
    ring
  have hdiff : ∀ w∈closedBall (0:ℂ) t, DifferentiableAt ℂ g w := by
    intro w hw
    exact (hg w (mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hw).trans_lt ht1))).differentiableAt
  have H := (convex_closedBall (0:ℂ) t).norm_image_sub_le_of_norm_deriv_le hdiff hd
    (mem_closedBall_self ht) (mem_closedBall_zero_iff.mpr hz)
  simp only [sub_zero] at H
  calc
    ‖g z-g 0‖ ≤ (512*M/(1-t))*‖z‖ := H
    _ ≤ (512*M/(1-t))*t := mul_le_mul_of_nonneg_left hz (by positivity)
    _ = 512*M*t/(1-t) := by ring

/-- An explicit (nonoptimal) Schottky majorant for functions omitting -1 and 1. -/
noncomputable def schottkyMajorant (R t : ℝ) : ℝ :=
  Real.exp (Real.pi*Real.exp (Real.pi*(1+(1+R/Real.pi)/Real.pi+1536*t/(1-t))))

/-- Schottky's estimate on the unit disc, using two cosine lifts and Bloch's theorem. -/
theorem norm_le_schottkyMajorant {f : ℂ → ℂ} {R t : ℝ}
    (ht : 0≤t) (ht1 : t<1)
    (hf : AnalyticOnNhd ℂ f (ball (0:ℂ) 1))
    (hplus : ∀ z∈ball (0:ℂ) 1, f z≠1)
    (hminus : ∀ z∈ball (0:ℂ) 1, f z≠-1)
    (hbase : ‖f 0‖≤R) {z : ℂ} (hz : ‖z‖≤t) :
    ‖f z‖≤schottkyMajorant R t := by
  have h0 : (0:ℂ)∈ball (0:ℂ) 1 := mem_ball_self (by norm_num)
  have hsc : IsSimplyConnected (ball (0:ℂ) 1) := by
    let : ContractibleSpace (ball (0:ℂ) 1) := (convex_ball (0:ℂ) 1).contractibleSpace ⟨0,h0⟩
    change SimplyConnectedSpace (ball (0:ℂ) 1)
    infer_instance
  obtain ⟨h,hh,hhbase,hhcos⟩ := exists_normalized_scaled_cosine_lift isOpen_ball hsc hf hplus hminus h0
  have hhone : ∀ w∈ball (0:ℂ) 1, h w≠1 := by
    intro w hw hval
    have H := hhcos w hw
    rw [hval,mul_one,Complex.cos_pi] at H
    exact hminus w hw H.symm
  have hhneg : ∀ w∈ball (0:ℂ) 1, h w≠-1 := by
    intro w hw hval
    have H := hhcos w hw
    rw [hval,mul_neg_one,Complex.cos_neg,Complex.cos_pi] at H
    exact hminus w hw H.symm
  obtain ⟨g,hg,hgbase,hgcos⟩ := exists_normalized_scaled_cosine_lift isOpen_ball hsc hh hhone hhneg h0
  have hdouble : ∀ w∈ball (0:ℂ) 1, Complex.cos (Real.pi*Complex.cos (Real.pi*g w))=f w := by
    intro w hw
    rw [hgcos w hw,hhcos w hw]
  have hno := no_ball_subset_double_cosine_lift_image hplus hminus hdouble
  have hvar := norm_sub_le_of_no_image_ball (by norm_num : (0:ℝ)≤3) ht ht1 hg hno hz
  have hg0 : ‖g 0‖≤1+(1+R/Real.pi)/Real.pi := by
    calc
      ‖g 0‖ ≤ 1+‖h 0‖/Real.pi := hgbase
      _ ≤ 1+(1+‖f 0‖/Real.pi)/Real.pi := by gcongr
      _ ≤ 1+(1+R/Real.pi)/Real.pi := by gcongr
  have hgz : ‖g z‖≤1+(1+R/Real.pi)/Real.pi+1536*t/(1-t) := by
    have H : ‖g z‖≤‖g z-g 0‖+‖g 0‖ := by
      simpa only [sub_add_cancel] using norm_add_le (g z-g 0) (g 0)
    norm_num at hvar
    linarith
  have hzU : z∈ball (0:ℂ) 1 := mem_ball_zero_iff.mpr (hz.trans_lt ht1)
  have hπnorm (w : ℂ) : ‖(Real.pi:ℂ)*w‖=Real.pi*‖w‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  calc
    ‖f z‖ = ‖Complex.cos (Real.pi*h z)‖ := congrArg norm (hhcos z hzU).symm
    _ ≤ Real.exp (Real.pi*‖h z‖) := by simpa only [hπnorm] using norm_cos_le_exp_norm (Real.pi*h z)
    _ ≤ Real.exp (Real.pi*Real.exp (Real.pi*‖g z‖)) := by
      have H : ‖h z‖≤Real.exp (Real.pi*‖g z‖) := by
        rw [← hgcos z hzU]
        simpa only [hπnorm] using norm_cos_le_exp_norm (Real.pi*g z)
      gcongr
    _ ≤ schottkyMajorant R t := by unfold schottkyMajorant; gcongr

end FunctionTheory
