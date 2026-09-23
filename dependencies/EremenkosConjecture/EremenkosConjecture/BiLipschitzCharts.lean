import EremenkosConjecture.UniformAmbientExtension
import EremenkosConjecture.ConformalEmbedding
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Holomorphic charts from quantitative ambient extensions -/

open Set Metric Function Filter
open scoped Topology NNReal

namespace EremenkosConjecture

theorem deriv_ne_zero_of_bilipschitz_extension {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (H : ℂ ≃ₜ ℂ)
    (hH : EqOn f H U) {L : ℝ≥0} (hL : LipschitzWith L H.symm)
    {x : ℂ} (hx : x ∈ U) : deriv f x ≠ 0 := by
  have hdiff := hf.differentiableAt (hU.mem_nhds hx)
  have ht : Tendsto (fun y => (L : ℝ) * ‖slope f x y‖) (𝓝[≠] x)
      (𝓝 ((L : ℝ) * ‖deriv f x‖)) := hdiff.hasDerivAt.tendsto_slope.norm.const_mul (L : ℝ)
  have he : ∀ᶠ y : ℂ in 𝓝[≠] x, 1 ≤ (L : ℝ) * ‖slope f x y‖ := by
    have hne : ∀ᶠ y : ℂ in 𝓝[≠] x, y ≠ x := self_mem_nhdsWithin
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx), hne] with y hy hyx
    have hb := hL.dist_le_mul (H y) (H x)
    rw [H.symm_apply_apply, H.symm_apply_apply, ← hH hy, ← hH hx] at hb
    have hdist : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
    rw [slope_def_field, norm_div]
    have h : 1 ≤ ((L : ℝ) * ‖f y - f x‖) / ‖y - x‖ :=
      (le_div_iff₀ hdist).mpr (by simpa only [one_mul, dist_eq_norm] using hb)
    simpa only [mul_div_assoc] using h
  have hl : 1 ≤ (L : ℝ) * ‖deriv f x‖ := ge_of_tendsto ht he
  intro hzero
  simp only [hzero, norm_zero, mul_zero] at hl
  linarith

theorem exists_conformal_chart_of_bilipschitz_extension {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (H : ℂ ≃ₜ ℂ)
    (hH : EqOn f H U) {L : ℝ≥0} (hL : LipschitzWith L H.symm) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, e.source = U ∧ e.target = f '' U ∧
      (∀ z, e z = f z) ∧ DifferentiableOn ℂ e.symm e.target := by
  apply exists_conformal_chart_of_injOn hU hf
  · intro x hx y hy he
    apply H.injective
    rwa [← hH hx, ← hH hy]
  · exact fun _ hx => deriv_ne_zero_of_bilipschitz_extension hU hf H hH hL hx

theorem differentiableOn_symm_of_holomorphic_extension {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (H : ℂ ≃ₜ ℂ)
    (hH : EqOn f H U) {L : ℝ≥0} (hL : LipschitzWith L H.symm) :
    DifferentiableOn ℂ H.symm (H '' U) := by
  obtain ⟨e, heS, heT, he, hei⟩ := exists_conformal_chart_of_bilipschitz_extension hU hf H hH hL
  have htarget : e.target = H '' U := heT.trans (image_congr hH)
  rw [htarget] at hei
  apply hei.congr
  intro w hw
  apply H.injective
  have hm : e.symm w ∈ U := by simpa only [heS] using e.map_target (htarget.symm ▸ hw)
  rw [H.apply_symm_apply, ← hH hm, ← he]
  exact (e.right_inv (htarget.symm ▸ hw)).symm

theorem exists_bilipschitz_approximation_tolerance_of_extension
    {U A : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U)
    (H : ℂ ≃ₜ ℂ) (heq : EqOn g H U) {L L' : ℝ≥0}
    (hL : LipschitzWith L H) (hL' : LipschitzWith L' H.symm)
    {r : ℝ} (hr : 0 < r) (htube : ∀ z ∈ A, ball z r ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
      (∀ z ∈ U, dist (f z) (g z) ≤ δ) →
      ∃ G : ℂ ≃ₜ ℂ, EqOn f G A ∧ ∃ M M' : ℝ≥0,
        LipschitzWith M G ∧ LipschitzWith M' G.symm := by
  have hA : A ⊆ U := fun z hz => htube z hz (mem_ball_self hr)
  obtain ⟨e, heS, heT, he, hei⟩ := exists_conformal_chart_of_bilipschitz_extension hU hg H heq hL'
  have heH : EqOn e H e.source := fun z hz => (he z).trans (heq (heS ▸ hz))
  have heA : e '' A = H '' A := image_congr (fun z hz => (he z).trans (heq (hA hz)))
  have heU : e.target = H '' U := heT.trans (image_congr heq)
  obtain ⟨s, hs, hstube⟩ := exists_uniform_image_tube H hL' hr htube
  obtain ⟨δ, hδ, hδall⟩ := exists_bilipschitz_approximation_tolerance e hei H heH hL hL'
    (A := A) (by simpa only [heS] using hA) hs (by simpa only [heA, heU] using hstube)
  refine ⟨δ, hδ, fun f hf hclose => ?_⟩
  apply hδall f (by simpa only [heS] using hf)
  intro z hz
  simpa only [he z] using hclose z (heS ▸ hz)

end EremenkosConjecture
