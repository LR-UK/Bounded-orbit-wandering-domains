import EremenkosConjecture.BiLipschitzCharts

/-! # Uniform iterate control supplied by ambient charts -/

open Set Metric Function
open scoped NNReal

namespace EremenkosConjecture

theorem UniformControlOn.mono_domain {g : ℂ → ℂ} {U V A : Set ℂ}
    (h : UniformControlOn g U A) (hUV : U ⊆ V) : UniformControlOn g V A := by
  intro ε hε
  obtain ⟨r, hr, hcontrol⟩ := h ε hε
  exact ⟨r, hr, fun z hz w hw => ⟨hUV (hcontrol z hz w hw).1, (hcontrol z hz w hw).2⟩⟩

theorem uniformControlOn_of_eqOn_lipschitz {f g : ℂ → ℂ} {U A : Set ℂ}
    {C : ℝ≥0} (hg : LipschitzWith C g) (heq : EqOn f g U)
    {r : ℝ} (hr : 0 < r) (htube : ∀ z ∈ A, ball z r ⊆ U) :
    UniformControlOn f U A := by
  intro ε hε
  refine ⟨min r (ε / ((C : ℝ) + 1)), lt_min hr (div_pos hε (by positivity)), ?_⟩
  intro z hz w hw
  have hzU := htube z hz (mem_ball_self hr)
  have hwU := htube z hz (hw.trans_le (min_le_left _ _))
  refine ⟨hwU, ?_⟩
  rw [heq hwU, heq hzU]
  have hb := hg.dist_le_mul w z
  have hs := (lt_div_iff₀ (by positivity : 0 < (C : ℝ) + 1)).mp
    (hw.trans_le (min_le_right _ _))
  exact hb.trans_lt (by nlinarith [dist_nonneg (x := w) (y := z)])

/-- If consecutive iterates agree with quantitative ambient charts on a
uniform neighbourhood, the original function has uniform control around the
intermediate orbit image. -/
theorem uniformControlOn_iterate_image {f : ℂ → ℂ} {k : ℕ}
    {U A E : Set ℂ} (H₀ H₁ : ℂ ≃ₜ ℂ)
    (h₀ : EqOn (f^[k]) H₀ U) (h₁ : EqOn (f^[k + 1]) H₁ U)
    {L₀ L₁ : ℝ≥0} (hL₀ : LipschitzWith L₀ H₀.symm) (hL₁ : LipschitzWith L₁ H₁)
    {r : ℝ} (hr : 0 < r) (htube : ∀ z ∈ A, ball z r ⊆ U)
    (himage : H₀ '' U ⊆ E) : UniformControlOn f E ((f^[k]) '' A) := by
  have hA : A ⊆ U := fun z hz => htube z hz (mem_ball_self hr)
  have heq : EqOn f (H₁ ∘ H₀.symm) (H₀ '' U) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Function.comp_apply, H₀.symm_apply_apply, ← h₀ hz, ← h₁ hz, iterate_succ_apply']
  obtain ⟨s, hs, hstube⟩ := exists_uniform_image_tube H₀ hL₀ hr htube
  have hc := (uniformControlOn_of_eqOn_lipschitz (hL₁.comp hL₀) heq hs hstube).mono_domain himage
  have himages : (f^[k]) '' A = H₀ '' A := image_congr (fun z hz => h₀ (hA hz))
  rwa [himages]

end EremenkosConjecture
