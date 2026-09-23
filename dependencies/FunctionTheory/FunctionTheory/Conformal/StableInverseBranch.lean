import FunctionTheory.Conformal.UnivalenceStability
import FunctionTheory.Analytic.UniformPreimageStability
import TauCeti.Analysis.Complex.Conformal.Biholomorph
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- A sufficiently small holomorphic perturbation of a conformal map retains
an inverse branch on a neighbourhood of any compact subset of its target.
The branch takes values in a relatively compact subset of the original source. -/
theorem exists_stable_inverse_branch_on_compact
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he : DifferentiableOn ℂ e e.source)
    (hei : DifferentiableOn ℂ e.symm e.target)
    {K : Set ℂ} (hK : IsCompact K) (hKT : K ⊆ e.target) :
    ∃ δ > 0, ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f e.source →
      (∀ z ∈ e.source, dist (f z) (e z) ≤ δ) →
      ∃ b : OpenPartialHomeomorph ℂ ℂ,
        K ⊆ b.source ∧ closure b.target ⊆ e.source ∧ IsCompact (closure b.target) ∧
        AnalyticOnNhd ℂ b b.source ∧
        (∀ w ∈ b.source, f (b w) = w) ∧
        ∀ z ∈ b.target, b (f z) = z := by
  have hL : IsCompact (e.symm '' K) :=
    hK.image_of_continuousOn (e.continuousOn_symm.mono hKT)
  have hLS : e.symm '' K ⊆ e.source := by
    rintro _ ⟨w, hw, rfl⟩
    exact e.map_target (hKT hw)
  obtain ⟨V, hV, hLV, hVS, hVc⟩ :=
    exists_open_between_and_isCompact_closure hL e.open_source hLS
  have hVS' : V ⊆ e.source := subset_closure.trans hVS
  obtain ⟨d₁, hd₁, Hinj⟩ := exists_injective_approximation_tolerance
    e hei (closure V) hVc hVS
  have hnc : ∀ a ∈ e.symm '' K, ¬ ∀ᶠ z in 𝓝 a, e z = e a := by
    intro a ha hconst
    have heq : (fun z => e z) =ᶠ[𝓝 a] (fun _ => e a) := hconst
    have hd := heq.deriv_eq
    simp only [deriv_const] at hd
    exact (TauCeti.deriv_ne_zero_of_injOn he e.open_source e.injOn (hLS ha)) hd
  obtain ⟨d₂, hd₂, Hcover⟩ := exists_uniform_stable_local_image
    hV hL hLV ((he.analyticOnNhd e.open_source).mono hVS') hnc
    (by norm_num : (0 : ℝ) < 1)
  refine ⟨min d₁ (d₂/2), lt_min hd₁ (half_pos hd₂), ?_⟩
  intro f hf hclose
  have hfi : InjOn f V :=
    (Hinj f hf.differentiableOn (fun z hz => (hclose z hz).trans (min_le_left _ _))).1.mono
      subset_closure
  have hfd : DifferentiableOn ℂ f V := (hf.mono hVS').differentiableOn
  let E := hfd.toOpenPartialHomeomorph hV hfi
  have hcover : K ⊆ E.target := by
    intro w hw
    have hwL : e.symm w ∈ e.symm '' K := mem_image_of_mem e.symm hw
    obtain ⟨z, hz, hzw⟩ := Hcover f (hf.mono hVS') (fun z hz => by
      have H := (hclose z (hVS' hz)).trans (min_le_right _ _)
      rw [dist_eq_norm, norm_sub_rev] at H
      exact H.trans_lt (half_lt_self hd₂))
      (e.symm w) hwL w (by rw [e.right_inv (hKT hw), sub_self, norm_zero]; exact hd₂)
    exact ⟨z, hz.1, hzw⟩
  refine ⟨E.symm, hcover, hVS, hVc, ?_, ?_, ?_⟩
  · exact (hfd.differentiableOn_toOpenPartialHomeomorph_symm hV hfi).analyticOnNhd
      E.open_target
  · intro w hw
    exact E.right_inv hw
  · intro z hz
    exact E.left_inv hz

end FunctionTheory
