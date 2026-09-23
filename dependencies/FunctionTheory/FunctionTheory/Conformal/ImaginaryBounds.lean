import TauCeti.Analysis.Complex.Conformal.NormalFamilies
import Mathlib.Analysis.Complex.BorelCaratheodory

open Set Metric

namespace FunctionTheory

theorem locallyBoundedOn_of_im_lower_bound
    {ι : Type*} {G : ι → ℂ → ℂ} {z₀ : ℂ} {M : ℝ}
    (hG : ∀ n, DifferentiableOn ℂ (G n) (ball 0 1))
    (hzero : ∀ n, G n 0 = z₀)
    (hbound : ∀ n, ∀ w ∈ ball 0 1, -M ≤ (G n w).im) :
    TauCeti.IsLocallyBoundedOn G (ball 0 1) := by
  let B : ℝ := |M| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hMb : M ≤ B := by dsimp [B]; linarith [le_abs_self M]
  have hpoint (n : ι) (w : ℂ) (hw : w ∈ ball 0 1) :
      ‖G n w‖ ≤ 2 * B * ‖w‖ / (1 - ‖w‖) + ‖z₀‖ * (1 + ‖w‖) / (1 - ‖w‖) := by
    have h := Complex.borelCaratheodory hB ((hG n).const_mul Complex.I)
      (show MapsTo (fun w => Complex.I * G n w) (ball 0 1) {z | z.re ≤ B} from by
        intro z hz
        simp only [mem_setOf_eq, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
          one_mul, zero_sub]
        linarith [hbound n z hz]) zero_lt_one hw
    simpa only [norm_mul, Complex.norm_I, one_mul, hzero n] using h
  intro K hKD hK
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, fun _ _ hz => False.elim hz⟩
  obtain ⟨a, ha, hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp (hKD ha)
  refine ⟨2 * B / (1 - ‖a‖) + 2 * ‖z₀‖ / (1 - ‖a‖), ?_⟩
  intro n w hw
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp (hKD hw)
  have hwa : ‖w‖ ≤ ‖a‖ := hmax hw
  apply (hpoint n w (hKD hw)).trans
  apply add_le_add
  · apply div_le_div₀ (by positivity) ?_ (by linarith) (by linarith)
    exact mul_le_of_le_one_right (by positivity) hw1.le
  · apply div_le_div₀ (by positivity) ?_ (by linarith) (by linarith)
    nlinarith [norm_nonneg z₀]

end FunctionTheory
