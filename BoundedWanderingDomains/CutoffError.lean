/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.LogKernelBounds

open Set Filter MeasureTheory InnerProductSpace Laplacian Metric
open scoped Topology ContDiff

namespace AreaDeficit

theorem logCutoff_laplacian_ne_zero {a z : ℂ} {A B : ℝ} (hAB : A < B)
    (hz : Δ (logCutoff a A B) z ≠ 0) :
    z ≠ a ∧ A < Real.log ‖z - a‖ ∧ Real.log ‖z - a‖ < B := by
  rw [laplacian_logCutoff_eq_kernel a z hAB] at hz
  have hk : logKernel A B (Real.log ‖z - a‖) ≠ 0 := (div_ne_zero_iff.mp hz).1
  refine ⟨?_, ?_, ?_⟩
  · intro he
    simp [he] at hz
  · exact lt_of_not_ge (fun h => hk (logKernel_eq_zero hAB (Or.inl h)))
  · exact lt_of_not_ge (fun h => hk (logKernel_eq_zero hAB (Or.inr h)))

/-- A pointwise relative error on the transition annulus controls its integral. -/
theorem integral_cutoff_error_le {f : ℂ → ℝ} (a : ℂ) {A B ε L : ℝ}
    (hAB : A < B) (hε : 0 ≤ ε)
    (hA : |A| ≤ L * (B - A)) (hB : |B| ≤ L * (B - A))
    (hf : ∀ z : ℂ, z ≠ a → A < Real.log ‖z - a‖ → Real.log ‖z - a‖ < B →
      |f z + Real.log ‖z - a‖| ≤ ε * |Real.log ‖z - a‖|) :
    |∫ z : ℂ, (f z + Real.log ‖z - a‖) * Δ (logCutoff a A B) z| ≤
      ε * (2 * Real.pi * L * ∫ s : ℝ, |transitionSecond s|) := by
  have hi : Integrable (fun z : ℂ => ε * |Real.log ‖z - a‖ * Δ (logCutoff a A B) z|) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_log_norm_laplacian_logCutoff a hAB).norm.const_mul ε
  have h := norm_integral_le_of_norm_le hi (ae_of_all volume (fun z => show
      ‖(f z + Real.log ‖z - a‖) * Δ (logCutoff a A B) z‖ ≤
        ε * |Real.log ‖z - a‖ * Δ (logCutoff a A B) z| from by
    by_cases hz : Δ (logCutoff a A B) z = 0
    · simp [hz]
    · obtain ⟨hza, hzA, hzB⟩ := logCutoff_laplacian_ne_zero hAB hz
      simpa only [Real.norm_eq_abs, abs_mul, mul_assoc] using
        mul_le_mul_of_nonneg_right (hf z hza hzA hzB) (abs_nonneg (Δ (logCutoff a A B) z))))
  rw [Real.norm_eq_abs, integral_const_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (integral_abs_log_norm_laplacian_logCutoff_le a hAB hA hB) hε)

/-- Uniformly vanishing logarithmic errors give the universal boundary contribution. -/
theorem tendsto_integral_cutoff {ι : Type*} {l : Filter ι} {f : ℂ → ℝ}
    (a : ℂ) {A B : ι → ℝ}
    (hAB : ∀ᶠ i in l, A i < B i)
    (hA : ∀ᶠ i in l, |A i| ≤ 2 * (B i - A i))
    (hB : ∀ᶠ i in l, |B i| ≤ 2 * (B i - A i))
    (hi : ∀ᶠ i in l, Integrable (fun z : ℂ => f z * Δ (logCutoff a (A i) (B i)) z))
    (hf : ∀ ε > 0, ∀ᶠ i in l, ∀ z : ℂ,
      z ≠ a → A i < Real.log ‖z - a‖ → Real.log ‖z - a‖ < B i →
      |f z + Real.log ‖z - a‖| ≤ ε * |Real.log ‖z - a‖|) :
    Tendsto (fun i => ∫ z : ℂ, f z * Δ (logCutoff a (A i) (B i)) z)
      l (𝓝 (-2 * Real.pi)) := by
  let M := 2 * Real.pi * 2 * ∫ s : ℝ, |transitionSecond s|
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (by positivity) (integral_nonneg (fun _ => abs_nonneg _))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hδ : 0 < ε / (M + 1) := div_pos hε (by linarith)
  filter_upwards [hAB, hA, hB, hi, hf (ε / (M + 1)) hδ] with i hiAB hiA hiB hii hif
  have hb := integral_cutoff_error_le a hiAB hδ.le hiA hiB hif
  have he : (∫ z : ℂ, (f z + Real.log ‖z - a‖) * Δ (logCutoff a (A i) (B i)) z) =
      (∫ z : ℂ, f z * Δ (logCutoff a (A i) (B i)) z) + 2 * Real.pi := by
    simp_rw [add_mul]
    rw [integral_add hii (integrable_log_norm_laplacian_logCutoff a hiAB),
      integral_log_norm_laplacian_logCutoff a hiAB]
  rw [he] at hb
  rw [Real.dist_eq]
  have hm : ε / (M + 1) * M < ε := by
    have : ε / (M + 1) * (M + 1) = ε := div_mul_cancel₀ ε (by linarith)
    nlinarith
  simpa only [sub_neg_eq_add, neg_mul] using hb.trans_lt hm

end AreaDeficit
