import FunctionTheory.Analytic.PreimageStability
import TauCeti.Analysis.Complex.Conformal.NormalFamilies
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.MeanValue

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Quantitative local image and univalence in Bloch's argument. A factor-two
derivative bound gives an injective smaller disc whose image contains an
explicit disc of radius r times the central derivative norm divided by 128. -/
theorem bloch_local_image_of_derivative_bound
    {f : ℂ → ℂ} {a : ℂ} {r : ℝ} (hr : 0<r)
    (hf : AnalyticOnNhd ℂ f (closedBall a r)) (hd0 : deriv f a≠0)
    (hbound : ∀ z∈closedBall a r, ‖deriv f z‖≤2*‖deriv f a‖) :
    ball (f a) (‖deriv f a‖*r/128) ⊆ f '' ball a (r/32) ∧
      InjOn f (ball a (r/32)) := by
  let A := ‖deriv f a‖
  let R := r/32
  have hA : 0<A := norm_pos_iff.mpr hd0
  have hR : 0<R := div_pos hr (by norm_num)
  have hhalf : 0<r/2 := half_pos hr
  have hhalfsub : closedBall a (r/2) ⊆ closedBall a r :=
    closedBall_subset_closedBall (by linarith)
  have hRhalf : closedBall a R ⊆ closedBall a (r/2) :=
    closedBall_subset_closedBall (by dsimp only [R]; linarith)
  have hRsub := hRhalf.trans hhalfsub
  have hsecond : ∀ z∈closedBall a (r/2), ‖deriv (deriv f) z‖≤4*A/r := by
    intro z hz
    have hsub : closedBall z (r/2) ⊆ closedBall a r :=
      closedBall_subset_closedBall' (by have := mem_closedBall.mp hz; linarith)
    have H := TauCeti.norm_deriv_le_of_forall_mem_closedBall_norm_le
      hf.deriv.differentiableOn hhalf hsub (fun w hw => hbound w (hsub hw))
    convert H using 1 <;> dsimp only [A] <;> ring
  have hvar : ∀ z∈closedBall a R, ‖deriv f z-deriv f a‖≤A/8 := by
    intro z hz
    have H := (convex_closedBall a (r/2)).norm_image_sub_le_of_norm_deriv_le
      (fun x hx => (hf.deriv x (hhalfsub hx)).differentiableAt) hsecond
      (mem_closedBall_self hhalf.le) (hRhalf hz)
    calc
      ‖deriv f z-deriv f a‖ ≤ (4*A/r)*‖z-a‖ := H
      _ ≤ (4*A/r)*R := mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.mp hz)
        (by positivity)
      _ = A/8 := by dsimp only [R]; field_simp; ring
  let u := fun z => f z-deriv f a*z
  have huD : ∀ z∈closedBall a R, DifferentiableAt ℂ u z := by
    intro z hz
    exact (hf z (hRsub hz)).differentiableAt.sub ((hasDerivAt_id z).const_mul (deriv f a)).differentiableAt
  have huBound : ∀ z∈closedBall a R, ‖deriv u z‖≤A/8 := by
    intro z hz
    have heq : deriv u z=deriv f z-deriv f a := by
      simpa only [u,mul_one,Pi.sub_def,id_eq] using ((hf z (hRsub hz)).differentiableAt.hasDerivAt.sub
        ((hasDerivAt_id z).const_mul (deriv f a))).deriv
    rw [heq]
    exact hvar z hz
  have hLip : ∀ x∈closedBall a R, ∀ y∈closedBall a R,
      ‖u x-u y‖≤(A/8)*‖x-y‖ := by
    intro x hx y hy
    exact (convex_closedBall a R).norm_image_sub_le_of_norm_deriv_le huD huBound hy hx
  let L := fun z => f a+deriv f a*(z-a)
  have hL : AnalyticOnNhd ℂ L univ :=
    analyticOnNhd_const.add (analyticOnNhd_const.mul (analyticOnNhd_id.sub analyticOnNhd_const))
  have hLa : L a=f a := by simp [L]
  have hmu : ∀ z∈sphere a R, A*R≤‖L z-L a‖ := by
    intro z hz
    have heq : L z-L a=deriv f a*(z-a) := by dsimp only [L]; ring
    rw [heq,norm_mul]
    have hzR : ‖z-a‖=R := mem_sphere_iff_norm.mp hz
    rw [hzR]
  have hclose : ∀ z∈sphere a R, ‖L z-f z‖<A*R/4 := by
    intro z hz
    have heq : L z-f z=-(u z-u a) := by dsimp only [L,u]; ring
    rw [heq,norm_neg]
    have H := hLip z (sphere_subset_closedBall hz) a (mem_closedBall_self hR.le)
    rw [mem_sphere_iff_norm.mp hz] at H
    exact H.trans_lt (by nlinarith [mul_pos hA hR])
  constructor
  · intro w hw
    have hw' : ‖w-L a‖<A*R/4 := by
      rw [hLa]
      have H : ‖w-f a‖<‖deriv f a‖*r/128 := mem_ball_iff_norm.mp hw
      convert H using 1 <;> dsimp only [A,R] <;> ring
    obtain ⟨z,hz,hzw⟩ := exists_preimage_of_circle_bound hR
      (hL.mono (subset_univ _)) (hf.mono hRsub) hmu
      (show 2*(A*R/4)<A*R by nlinarith [mul_pos hA hR]) hclose hw'
    exact ⟨z,hz,hzw⟩
  · intro x hx y hy hxy
    have H := hLip x (ball_subset_closedBall hx) y (ball_subset_closedBall hy)
    have heq : deriv f a*(x-y)=-(u x-u y) := by
      dsimp only [u]
      rw [hxy]
      ring
    have Hnorm := congrArg norm heq
    rw [norm_mul,norm_neg] at Hnorm
    by_contra hne
    have hdist : 0<‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hp := mul_pos hA hdist
    change 0<A*‖x-y‖ at hp
    change A*‖x-y‖=‖u x-u y‖ at Hnorm
    nlinarith

end FunctionTheory
