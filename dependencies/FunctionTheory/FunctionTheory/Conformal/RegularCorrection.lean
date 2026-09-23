import FunctionTheory.Conformal.LocalUnivalenceStability
import FunctionTheory.Conformal.CorrectionGluing
import FunctionTheory.Analytic.UniformPreimageStability

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- The regular case of the conformal correction lemma: on a relatively compact
open set free of critical points, every sufficiently close holomorphic map is
related to the reference map by a near-identity conformal change of coordinates.
All interpolated points are fixed. -/
theorem exists_conformal_correction_of_deriv_ne_zero
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact (closure V)) (hKU : closure V ⊆ U)
    {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ U)
    (hd : ∀ a ∈ closure V, deriv φ a ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g U →
      (∀ z ∈ U, ‖φ z - g z‖ ≤ δ) →
      ∃ θ : ℂ → ℂ, AnalyticOnNhd ℂ θ V ∧ InjOn θ V ∧ MapsTo θ V U ∧
        DifferentiableOn ℂ (Function.invFunOn θ V) (θ '' V) ∧
        (∀ a ∈ V, ‖θ a - a‖ < ε ∧ g (θ a) = φ a) ∧
        (∀ a ∈ V, g a = φ a → θ a = a) := by
  obtain ⟨R, hR, δ₁, hδ₁, Hφ, Hg⟩ :=
    exists_uniform_injective_approximation_radius hU hK hKU hφ hd
  let r := min R ε
  have hr : 0 < r := lt_min hR hε
  have hrR : r ≤ R := min_le_left _ _
  have hrε : r ≤ ε := min_le_right _ _
  have hnc : ∀ a ∈ closure V, ¬ ∀ᶠ z in 𝓝 a, φ z = φ a := by
    intro a ha hconst
    have heq : φ =ᶠ[𝓝 a] (fun _ => φ a) := hconst
    apply hd a ha
    simpa only [deriv_const] using heq.deriv_eq
  obtain ⟨δ₂, hδ₂, Hroot⟩ := exists_uniform_stable_local_image hU hK hKU hφ hnc
    (half_pos hr)
  have hmin : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have htol₁ : min δ₁ δ₂ / 2 < δ₁ :=
    (half_lt_self hmin).trans_le (min_le_left _ _)
  have htol₂ : min δ₁ δ₂ / 2 < δ₂ :=
    (half_lt_self hmin).trans_le (min_le_right _ _)
  refine ⟨min δ₁ δ₂ / 2, half_pos hmin, ?_⟩
  intro g hg hclose
  have hclose₁ : ∀ z ∈ U, ‖φ z - g z‖ < δ₁ :=
    fun z hz => (hclose z hz).trans_lt htol₁
  have hclose₂ : ∀ z ∈ U, ‖φ z - g z‖ < δ₂ :=
    fun z hz => (hclose z hz).trans_lt htol₂
  have hVU : V ⊆ U := subset_closure.trans hKU
  have htube : ∀ a ∈ V, ball a r ⊆ U :=
    fun a ha => (ball_subset_ball hrR).trans (Hφ a (subset_closure ha)).1
  have hgi : ∀ a ∈ V, InjOn g (ball a r) :=
    fun a ha => (Hg g hg hclose₁ a (subset_closure ha)).mono (ball_subset_ball hrR)
  have hφi : ∀ a ∈ V, InjOn φ (V ∩ ball a r) :=
    fun a ha => (Hφ a (subset_closure ha)).2.mono
      (inter_subset_right.trans (ball_subset_ball hrR))
  have hroots : ∀ a ∈ V, ∃ w : ℂ, dist w a < r / 2 ∧ g w = φ a := by
    intro a ha
    obtain ⟨w, hw, heq⟩ := Hroot g hg hclose₂ a (subset_closure ha) (φ a)
      (by simpa only [sub_self, norm_zero] using hδ₂)
    exact ⟨w, mem_ball.mp hw.2, heq⟩
  obtain ⟨θ, hθA, hθi, hθU, hθeq, hfixed⟩ :=
    exists_conformal_correction_of_uniform_local_injectivity hV (hφ.mono hVU) hg
      hr htube hgi hφi hroots
  refine ⟨θ, hθA, hθi, hθU, hθA.differentiableOn.invFunOn hV hθi, ?_, hfixed⟩
  intro a ha
  exact ⟨by simpa only [dist_eq_norm] using
    (hθeq a ha).1.trans ((half_lt_self hr).trans_le hrε), (hθeq a ha).2⟩

end FunctionTheory
