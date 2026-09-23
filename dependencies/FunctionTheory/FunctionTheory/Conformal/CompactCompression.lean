import FunctionTheory.Conformal.ContinuousPostcomposition
import FunctionTheory.Conformal.ThinAttachmentEscape
import Mathlib.Analysis.Normed.Group.Bounded

open Set Metric Filter Complex
open scoped Topology

namespace FunctionTheory

/-- A single positive scale controls a compact part of all sufficiently
late maps in a locally uniformly convergent family. -/
theorem exists_uniform_scale_on_compact_of_locallyUniform
    {V K : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {r ε : ℝ}
    (hconv : TendstoLocallyUniformlyOn F f atTop V) (hf : ContinuousOn f V)
    (hK : IsCompact K) (hKV : K ⊆ V) (hr : 0 < r) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ c * (Real.pi / 2) < r ∧
      ∀ᶠ n in atTop, ∀ z ∈ K, ‖(c : ℂ) * F n z‖ < ε := by
  obtain ⟨B, hB, hbound⟩ := (hK.image_of_continuousOn (hf.mono hKV)).isBounded.exists_pos_norm_le
  let c := min (r / (Real.pi + 1)) (ε / (2 * (B + 1)))
  have hc : 0 < c := lt_min (div_pos hr (by linarith [Real.pi_pos])) (by positivity)
  have hc₁ : c * (Real.pi + 1) ≤ r :=
    (le_div_iff₀ (by linarith [Real.pi_pos])).mp (min_le_left _ _)
  have hc₂ : c * (2 * (B + 1)) ≤ ε :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hu : TendstoUniformlyOn F f atTop K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (hconv.mono hKV)
  refine ⟨c, hc, by nlinarith [Real.pi_pos], ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu 1 zero_lt_one] with n hn
  intro z hz
  have hclose : ‖F n z - f z‖ < 1 := by
    rw [norm_sub_rev]
    simpa only [dist_eq_norm] using hn z hz
  have hb : ‖f z‖ ≤ B := hbound _ (mem_image_of_mem f hz)
  have hFn : ‖F n z‖ < B + 1 := by
    have h := norm_add_le (F n z - f z) (f z)
    rw [sub_add_cancel] at h
    linarith
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hc]
  nlinarith

/-- Compact compression and uniform leftward escape can be imposed
simultaneously by one scale and one member of the family. -/
theorem exists_scaled_map_with_compact_control_and_left_escape
    {V K X : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {r ε : ℝ}
    (hconv : TendstoLocallyUniformlyOn F f atTop V) (hf : ContinuousOn f V)
    (hK : IsCompact K) (hKV : K ⊆ V) (hr : 0 < r) (hε : 0 < ε)
    (hleft : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ x ∈ X, (F n x).re < M)
    (M : ℝ) :
    ∃ (c : ℝ) (n : ℕ), 0 < c ∧ c * (Real.pi / 2) < r ∧
      (∀ z ∈ K, ‖(c : ℂ) * F n z‖ < ε) ∧
      ∀ x ∈ X, ((c : ℂ) * F n x).re < M := by
  obtain ⟨c, hc, hcr, hcompact⟩ :=
    exists_uniform_scale_on_compact_of_locallyUniform hconv hf hK hKV hr hε
  have hscaled : ∀ᶠ n in atTop, ∀ x ∈ X, ((c : ℂ) * F n x).re < M := by
    simpa only [add_zero] using uniform_left_escape_affine (b := 0) hc hleft M
  obtain ⟨n, hnK, hnX⟩ := (hcompact.and hscaled).exists
  exact ⟨c, n, hc, hcr, hnK, hnX⟩

end FunctionTheory
