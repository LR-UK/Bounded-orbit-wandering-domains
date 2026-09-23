import FunctionTheory.Smooth.FiniteSmoothNorm
import FunctionTheory.Smooth.HolomorphicSmoothExtension
import FunctionTheory.Holomorphic

open Set Function Filter
open scoped Topology ContDiff

namespace FunctionTheory

set_option autoImplicit false

/-- Compact extension in the uniform C^m norm, including the zeroth order.
The local map is smooth; small C^m displacement, with m ≥ 1, supplies
injectivity of its global extension. -/
theorem exists_smooth_extension_in_Cm_norm
    {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (m : ℕ) (hm : 1 ≤ m) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ θ : ℂ → ℂ, ContDiffOn ℝ ∞ θ U →
      finiteSmoothNormOn m (fun w => θ w - w) U ≤ ENNReal.ofReal δ →
      ∃ e : ℂ ≃ₜ ℂ,
        ContDiff ℝ ∞ (e : ℂ → ℂ) ∧ ContDiff ℝ ∞ (e.symm : ℂ → ℂ) ∧
        (∀ z ∈ K, (e : ℂ → ℂ) =ᶠ[𝓝 z] θ) ∧
        (∀ z ∉ U, e z = z) ∧
        HasCompactSupport (fun z => e z - z) ∧
        tsupport (fun z => e z - z) ⊆ U ∧
        finiteSmoothNormOn m (fun w => e w - w) univ < ENNReal.ofReal ε := by
  let b : ℝ := ε / (2 * (m + 1 : ℕ))
  have hb : 0 < b := div_pos hε (by positivity)
  obtain ⟨δ, hδ, Hδ⟩ := exists_controlled_smooth_extension hK hU hKU m hm hb
  refine ⟨δ, hδ, ?_⟩
  intro θ hθ Hθ
  obtain ⟨e, hes, hei, heK, heU, hec, hesupp, heBound⟩ :=
    Hδ θ hθ (fun n hn z hz =>
      norm_iteratedFDeriv_le_of_finiteSmoothNormOn_le hδ.le Hθ hn hz)
  refine ⟨e, hes, hei, heK, heU, hec, hesupp, ?_⟩
  exact finiteSmoothNormOn_lt_of_uniform_margin hε
    (fun n hn z _ => (heBound n hn z).le)

/-- Holomorphic compact extension with a controlled C^m change after
composition with a fixed C^m homeomorphism. In particular this applies
to the diffeomorphisms in the successive-conjugacy construction. -/
theorem exists_holomorphic_extension_comp_in_Cm_norm
    (Θ : ℂ ≃ₜ ℂ) (m : ℕ) (hΘ : ContDiff ℝ m (Θ : ℂ → ℂ))
    {X V : Set ℂ} (hX : IsCompact X) (hV : IsOpen V) (hXV : Θ '' X ⊆ V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ θ : ℂ → ℂ, AnalyticOnNhd ℂ θ V →
      (∀ z ∈ V, ‖θ z - z‖ ≤ η) →
      ∃ e : ℂ ≃ₜ ℂ,
        ContDiff ℝ ∞ (e : ℂ → ℂ) ∧ ContDiff ℝ ∞ (e.symm : ℂ → ℂ) ∧
        (∀ z ∈ Θ '' X, (e : ℂ → ℂ) =ᶠ[𝓝 z] θ) ∧
        (∀ z ∉ V, e z = z) ∧
        HasCompactSupport (fun z => e z - z) ∧
        tsupport (fun z => e z - z) ⊆ V ∧
        finiteSmoothNormOn m (fun w => e (Θ w) - Θ w) univ < ENNReal.ofReal ε := by
  let b : ℝ := ε / (2 * (m + 1 : ℕ))
  have hb : 0 < b := div_pos hε (by positivity)
  obtain ⟨η, hη, Hη⟩ := exists_holomorphic_smooth_extension_comp Θ m hΘ hX hV hXV hb
  refine ⟨η, hη, ?_⟩
  intro θ hθ Hθ
  obtain ⟨e, hes, hei, heK, heV, hec, hesupp, heBound⟩ := Hη θ hθ Hθ
  refine ⟨e, hes, hei, heK, heV, hec, hesupp, ?_⟩
  exact finiteSmoothNormOn_lt_of_uniform_margin hε
    (fun n hn z _ => (heBound n hn z).le)

/-- The holomorphic extension theorem for a function defined only on its
actual open domain. Values outside that domain are not part of the input. -/
theorem exists_holomorphic_extension_on_domain_comp_in_Cm_norm
    (Θ : ℂ ≃ₜ ℂ) (m : ℕ) (hΘ : ContDiff ℝ m (Θ : ℂ → ℂ))
    {X V : Set ℂ} (hX : IsCompact X) (hV : IsOpen V) (hXV : Θ '' X ⊆ V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ θ : V → ℂ, IsHolomorphicFunctionOn V θ →
      (∀ z : V, ‖θ z - (z : ℂ)‖ ≤ η) →
      ∃ e : ℂ ≃ₜ ℂ,
        ContDiff ℝ ∞ (e : ℂ → ℂ) ∧ ContDiff ℝ ∞ (e.symm : ℂ → ℂ) ∧
        (∀ a ∈ Θ '' X, ∀ᶠ z in 𝓝 a, ∀ hz : z ∈ V, e z = θ ⟨z, hz⟩) ∧
        (∀ z ∉ V, e z = z) ∧
        HasCompactSupport (fun z => e z - z) ∧
        tsupport (fun z => e z - z) ⊆ V ∧
        finiteSmoothNormOn m (fun w => e (Θ w) - Θ w) univ < ENNReal.ofReal ε := by
  obtain ⟨η, hη, Hη⟩ := exists_holomorphic_extension_comp_in_Cm_norm Θ m hΘ hX hV hXV hε
  refine ⟨η, hη, ?_⟩
  intro θ hθ Hθ
  have hθA := (hθ.differentiableOn_extension hV).analyticOnNhd hV
  have Hbound : ∀ z ∈ V, ‖domainExtension θ z - z‖ ≤ η := by
    intro z hz
    simpa only [domainExtension_apply θ z hz] using Hθ ⟨z, hz⟩
  obtain ⟨e, hes, hei, heK, heV, hec, hesupp, heBound⟩ :=
    Hη (domainExtension θ) hθA Hbound
  refine ⟨e, hes, hei, ?_, heV, hec, hesupp, heBound⟩
  intro a ha
  filter_upwards [heK a ha] with z hz
  intro hzV
  exact hz.trans (domainExtension_apply θ z hzV)

end FunctionTheory
