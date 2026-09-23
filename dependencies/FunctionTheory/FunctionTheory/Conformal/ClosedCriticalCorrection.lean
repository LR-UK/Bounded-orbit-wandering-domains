import FunctionTheory.Analytic.CriticalNeighborhood
import FunctionTheory.Conformal.FiniteCriticalCorrection

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- The correction lemma only needs critical-point control on the closed
source, since isolated critical points allow the working neighbourhood to
be shrunk. This is the boundary-safe version needed for finite chains. -/
theorem exists_conformal_correction_of_critical_control_on_closure_order_le
    {U V C : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact (closure V)) (hKU : closure V ⊆ U)
    (hC : C.Finite) (hCV : C ⊆ V) {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ U)
    (hcritical : ∀ z ∈ closure V, deriv φ z = 0 → z ∈ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g U →
      (∀ c ∈ C, g c = φ c) →
      (∀ c ∈ C, analyticOrderAt (fun z => φ z - φ c) c ≤
        analyticOrderAt (fun z => g z - g c) c) →
      (∀ z ∈ U, ‖φ z - g z‖ ≤ δ) →
      ∃ θ : ℂ → ℂ, AnalyticOnNhd ℂ θ V ∧ InjOn θ V ∧ MapsTo θ V U ∧
        DifferentiableOn ℂ (Function.invFunOn θ V) (θ '' V) ∧
        (∀ z ∈ V, ‖θ z - z‖ < ε ∧ g (θ z) = φ z) ∧ ∀ c ∈ C, θ c = c := by
  have hncV := locally_nonconstant_of_finite_critical_set hV hC
    (fun z hz => hcritical z (subset_closure hz))
  have hncK : ∀ a ∈ closure V, ¬ ∀ᶠ z in 𝓝 a, φ z = φ a := by
    intro a ha hconst
    have heq : φ =ᶠ[𝓝 a] (fun _ => φ a) := hconst
    have hd : deriv φ a = 0 := by simpa only [deriv_const] using heq.deriv_eq
    exact hncV a (hCV (hcritical a ha hd)) hconst
  obtain ⟨W, hW, hKW, hWU, _, hWcritical⟩ :=
    exists_critical_control_neighborhood hK hU hKU hφ hncK hcritical
  have hWU' : W ⊆ U := subset_closure.trans hWU
  obtain ⟨δ, hδ, H⟩ := exists_conformal_correction_of_finite_critical_set_order_le
    hW hV hK hKW hC hCV (hφ.mono hWU')
    (fun z hz => hWcritical z (subset_closure hz)) hε
  refine ⟨δ, hδ, ?_⟩
  intro g hg hvalue horder hclose
  obtain ⟨θ, hθA, hθi, hθW, hθinv, hpair, hfixed⟩ :=
    H g (hg.mono hWU') hvalue horder (fun z hz => hclose z (hWU' hz))
  exact ⟨θ, hθA, hθi, hθW.mono_right hWU', hθinv, hpair, hfixed⟩

/-- The finite conformal-correction lemma in critical-multiplicity form.
Only critical points of the reference map need multiplicity constraints;
the remaining marked points need only value interpolation. -/
theorem exists_conformal_correction_of_critical_control_on_closure
    {U V C : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact (closure V)) (hKU : closure V ⊆ U)
    (hC : C.Finite) (hCV : C ⊆ V) {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ U)
    (hcritical : ∀ z ∈ closure V, deriv φ z = 0 → z ∈ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g U →
      (∀ c ∈ C, g c = φ c) →
      (∀ c ∈ V, deriv φ c = 0 →
        analyticOrderAt (deriv g) c = analyticOrderAt (deriv φ) c) →
      (∀ z ∈ U, ‖φ z - g z‖ ≤ δ) →
      ∃ θ : ℂ → ℂ, AnalyticOnNhd ℂ θ V ∧ InjOn θ V ∧ MapsTo θ V U ∧
        DifferentiableOn ℂ (Function.invFunOn θ V) (θ '' V) ∧
        (∀ z ∈ V, ‖θ z - z‖ < ε ∧ g (θ z) = φ z) ∧ ∀ c ∈ C, θ c = c := by
  obtain ⟨δ, hδ, H⟩ := exists_conformal_correction_of_critical_control_on_closure_order_le
    hU hV hK hKU hC hCV hφ hcritical hε
  refine ⟨δ, hδ, ?_⟩
  intro g hg hvalue hmult hclose
  apply H g hg hvalue _ hclose
  intro c hc
  have hcU := hKU (subset_closure (hCV hc))
  by_cases hdc : deriv φ c = 0
  · exact (analyticOrderAt_sub_eq_of_deriv_order_eq (hφ c hcU) (hg c hcU)
      (hmult c (hCV hc) hdc).symm).le
  · rw [(hφ c hcU).analyticOrderAt_sub_eq_one_of_deriv_ne_zero hdc]
    have hG : AnalyticAt ℂ (fun z => g z - g c) c := (hg c hcU).sub analyticAt_const
    exact Order.one_le_iff_ne_zero.mpr (hG.analyticOrderAt_ne_zero.mpr (sub_self (g c)))

end FunctionTheory

