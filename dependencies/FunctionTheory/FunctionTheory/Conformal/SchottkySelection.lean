import FunctionTheory.Conformal.SchottkyDisc
import Mathlib.Order.Filter.AtTopBot.Basic

open Set Metric Filter
namespace FunctionTheory
set_option autoImplicit false

/-- On a half-sized disc, a sequence omitting zero and one has a
uniformly bounded subsequence of either the functions or their reciprocals.
This is the local analytic input to omitted-values normality. -/
theorem exists_bounded_subsequence_or_inverse_on_disc
    {F : ℕ → ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0<r)
    (hF : ∀ n, AnalyticOnNhd ℂ (F n) (ball c r))
    (hzero : ∀ n z, z∈ball c r → F n z≠0)
    (hone : ∀ n z, z∈ball c r → F n z≠1) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ((∀ n z, z∈ball c (r/2) → ‖F (σ n) z‖≤schottkyZeroOneMajorant 1 (1/2)) ∨
       (∀ n z, z∈ball c (r/2) → ‖(F (σ n) z)⁻¹‖≤schottkyZeroOneMajorant 1 (1/2))) := by
  have hcase : ∀ n, ‖F n c‖≤1 ∨ ‖(F n c)⁻¹‖≤1 := by
    intro n
    by_cases h : ‖F n c‖≤1
    · exact Or.inl h
    · right
      rw [norm_inv]
      exact (inv_le_one₀ (by linarith : 0<‖F n c‖)).mpr (le_of_not_ge h)
  have hfreq : (∃ᶠ n in atTop, ‖F n c‖≤1) ∨ (∃ᶠ n in atTop, ‖(F n c)⁻¹‖≤1) :=
    frequently_or_distrib.mp (Frequently.of_forall hcase)
  have hdist {z : ℂ} (hz : z∈ball c (r/2)) : ‖z-c‖≤(1/2)*r := by
    have H := mem_ball_iff_norm.mp hz
    linarith
  rcases hfreq with h | h
  · obtain ⟨σ,hσ,hbase⟩ := extraction_of_frequently_atTop h
    refine ⟨σ,hσ,Or.inl ?_⟩
    intro n z hz
    exact norm_le_schottkyZeroOneMajorant_on_disc hr (by norm_num) (by norm_num)
      (hF (σ n)) (hzero (σ n)) (hone (σ n)) (hbase n) (hdist hz)
  · obtain ⟨σ,hσ,hbase⟩ := extraction_of_frequently_atTop h
    refine ⟨σ,hσ,Or.inr ?_⟩
    intro n z hz
    have hG : AnalyticOnNhd ℂ (fun w => (F (σ n) w)⁻¹) (ball c r) :=
      (hF (σ n)).inv (hzero (σ n))
    exact norm_le_schottkyZeroOneMajorant_on_disc hr (by norm_num) (by norm_num)
      hG (fun w hw => inv_ne_zero (hzero (σ n) w hw))
      (fun w hw H => hone (σ n) w hw (inv_eq_one.mp H)) (hbase n) (hdist hz)

end FunctionTheory
