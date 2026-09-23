import ComplexApproximation.BiLipschitzExtension
import ComplexApproximation.HalfStripBounds

/-! # Ambient extension of the explicit conformal half-strip map -/

open Set Complex
open scoped NNReal

namespace ComplexApproximation.HalfStrip

theorem exists_bilipschitz_extension {η b : ℝ} (hη : 0 < η) (hb : 0 ≤ b)
    (hbpi : b < Real.pi / 2) :
    ∃ H : ℂ ≃ₜ ℂ, EqOn map H (closedRightHalfStrip η b) ∧ ∃ L L' : ℝ≥0,
      LipschitzWith L H ∧ LipschitzWith L' H.symm := by
  have hsub : closedRightHalfStrip η b ⊆ domain := fun z hz =>
    ⟨hη.trans_le hz.1, hz.2.trans_lt hbpi⟩
  let q := Real.exp (-2 * η)
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hm : 0 < (1 - q) / (1 + q) := div_pos (sub_pos.mpr hq) (by dsimp [q]; positivity)
  apply exists_bilipschitz_extension_of_positive_derivative
    (convex_closedRightHalfStrip η b) (lipschitzWith_halfStripProjection η b)
    (fun z _ => halfStripProjection_mem η hb z)
    (fun _ hz => halfStripProjection_eq hz)
    (fun _ hz => (hasDerivAt_map (hsub hz)).differentiableAt) hm
  intro z hz
  exact ⟨re_derivative_lower_bound hη (hsub hz) hz.1,
    (derivative_bounds hη (hsub hz) hz.1).2⟩

end ComplexApproximation.HalfStrip
