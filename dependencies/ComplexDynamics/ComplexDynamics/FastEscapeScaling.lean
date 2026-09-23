import ComplexDynamics.FastEscape
import ComplexDynamics.Scaling

/-! # Scaling of maximum modulus and fast escape -/

open Set Metric Function Filter

namespace ComplexDynamics

theorem maximumModulus_scaleConjugate {f : ℂ → ℂ} (hf : Continuous f)
    (c : ℂ) (hc : c ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    maximumModulus (scaleConjugate c f) (‖c‖ * r) = ‖c‖ * maximumModulus f r := by
  have hcpos := norm_pos_iff.mpr hc
  have hF : Continuous (scaleConjugate c f) :=
    (hf.comp (continuous_const.mul continuous_id)).const_mul c
  apply le_antisymm
  · apply maximumModulus_le (mul_nonneg (norm_nonneg c) hr)
    intro z hz
    have hz' : ‖z‖ ≤ ‖c‖ * r := by simpa only [mem_closedBall, dist_zero_right] using hz
    have hw : c⁻¹ * z ∈ closedBall 0 r := by
      simp only [mem_closedBall, dist_zero_right, norm_mul, norm_inv]
      rw [mul_comm, ← div_eq_mul_inv]
      exact (div_le_iff₀ hcpos).mpr (by simpa only [mul_comm] using hz')
    simpa only [scaleConjugate, norm_mul] using
      mul_le_mul_of_nonneg_left (norm_le_maximumModulus hf hw) (norm_nonneg c)
  · have H : maximumModulus f r ≤ maximumModulus (scaleConjugate c f) (‖c‖ * r) / ‖c‖ := by
      apply maximumModulus_le hr
      intro z hz
      have hz' : c * z ∈ closedBall 0 (‖c‖ * r) := by
        simp only [mem_closedBall, dist_zero_right, norm_mul] at hz ⊢
        exact mul_le_mul_of_nonneg_left hz (norm_nonneg c)
      have H := norm_le_maximumModulus hF hz'
      apply (le_div_iff₀ hcpos).mpr
      change ‖c * f (c⁻¹ * (c * z))‖ ≤ _ at H
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul, norm_mul] at H
      simpa only [mul_comm] using H
    simpa only [mul_comm] using (le_div_iff₀ hcpos).mp H

theorem maximumModulus_iterate_nonneg {f : ℂ → ℂ} (hf : Continuous f)
    {r : ℝ} (hr : 0 ≤ r) (n : ℕ) : 0 ≤ ((maximumModulus f)^[n]) r := by
  induction n with
  | zero => exact hr
  | succ n ih =>
    rw [iterate_succ_apply']
    exact maximumModulus_nonneg hf ih

theorem iterate_maximumModulus_scaleConjugate {f : ℂ → ℂ} (hf : Continuous f)
    (c : ℂ) (hc : c ≠ 0) {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    ((maximumModulus (scaleConjugate c f))^[n]) (‖c‖ * r) =
      ‖c‖ * ((maximumModulus f)^[n]) r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply',
      maximumModulus_scaleConjugate hf c hc (maximumModulus_iterate_nonneg hf hr n)]

theorem mapsTo_scale_fastEscapingSetAtRadius {f : ℂ → ℂ} (hf : Continuous f)
    (c : ℂ) (hc : c ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    MapsTo (fun z => c * z) (fastEscapingSetAtRadius f r)
      (fastEscapingSetAtRadius (scaleConjugate c f) (‖c‖ * r)) := by
  intro z hz
  refine ⟨?_, ?_⟩
  · change Tendsto (fun n => ‖((scaleConjugate c f)^[n]) (c * z)‖) atTop atTop
    simp only [iterate_scaleConjugate_mul c hc, norm_mul]
    exact hz.1.const_mul_atTop (norm_pos_iff.mpr hc)
  · obtain ⟨l, hl⟩ := hz.2
    refine ⟨l, fun n => ?_⟩
    rw [iterate_maximumModulus_scaleConjugate hf c hc hr,
      iterate_scaleConjugate_mul c hc, norm_mul]
    exact mul_le_mul_of_nonneg_left (hl n) (norm_nonneg c)

end ComplexDynamics
