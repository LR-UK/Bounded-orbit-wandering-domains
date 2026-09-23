import FunctionTheory.Conformal.BlochSelection
import FunctionTheory.Conformal.BlochLocalImage

open Set Metric

namespace FunctionTheory

set_option autoImplicit false

/-- Bloch's theorem on the unit disc, with explicit constant 1/256. The
image disc has a univalent inverse branch on a smaller source disc. -/
theorem exists_bloch_disc_of_analytic_closedUnitDisc
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall (0:ℂ) 1))
    (hd : deriv f 0≠0) :
    ∃ a : ℂ, ∃ r : ℝ, 0<r ∧ ball a r ⊆ ball (0:ℂ) 1 ∧
      InjOn f (ball a r) ∧ ball (f a) (‖deriv f 0‖/256) ⊆ f '' ball a r := by
  obtain ⟨a,r,hr,hsub,hda,hprod,hbound⟩ := exists_bloch_selection hf.deriv.continuousOn hd
  obtain ⟨himage,hinj⟩ := bloch_local_image_of_derivative_bound hr
    (hf.mono (hsub.trans ball_subset_closedBall)) hda hbound
  refine ⟨a,r/32,by positivity,?_,hinj,?_⟩
  · exact ball_subset_closedBall.trans
      ((closedBall_subset_closedBall (by linarith : r/32≤r)).trans hsub)
  · apply Subset.trans (ball_subset_ball ?_) himage
    nlinarith

end FunctionTheory
