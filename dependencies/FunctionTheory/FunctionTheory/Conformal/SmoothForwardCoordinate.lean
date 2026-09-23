import FunctionTheory.Smooth.ExtensionNorm
import TauCeti.Analysis.Complex.Conformal.Biholomorph

open Set Function Filter
open scoped Topology ContDiff

namespace FunctionTheory

set_option autoImplicit false

/-- Smoothly extend a forward coordinate F composed with a conformal
inverse. The estimate is on the original source; the smooth extension is
supported in the chosen target neighbourhood. -/
theorem exists_smooth_forward_coordinate_tolerance
    (Θ : ℂ ≃ₜ ℂ) (m : ℕ) (hΘ : ContDiff ℝ m (Θ : ℂ → ℂ))
    {X V C : Set ℂ} (hX : IsCompact X) (hV : IsOpen V) (hXV : Θ '' X ⊆ V)
    (hCX : C ⊆ Θ '' X) (e : OpenPartialHomeomorph ℂ ℂ)
    (hVe : V ⊆ e.target) (hei : AnalyticOnNhd ℂ e.symm e.target)
    {ε : ℝ} (hε : 0<ε) :
    ∃ η>0, ∀ F : ℂ → ℂ, AnalyticOnNhd ℂ F (e.symm '' V) →
      (∀ x∈e.symm '' V, ‖F x-e x‖≤η) →
      (∀ c∈C, F (e.symm c)=c) →
      ∃ E : ℂ ≃ₜ ℂ,
        ContDiff ℝ ∞ (E : ℂ → ℂ) ∧ ContDiff ℝ ∞ (E.symm : ℂ → ℂ) ∧
        (∀ z∈Θ '' X, (E : ℂ → ℂ) =ᶠ[𝓝 z] (F ∘ e.symm)) ∧
        EqOn (E : ℂ → ℂ) id C ∧
        (∀ z∉V, E z=z) ∧ HasCompactSupport (fun z => E z-z) ∧
        tsupport (fun z => E z-z) ⊆ V ∧
        finiteSmoothNormOn m (fun z => E (Θ z)-Θ z) univ<ENNReal.ofReal ε := by
  obtain ⟨η,hη,Hη⟩ := exists_holomorphic_extension_comp_in_Cm_norm Θ m hΘ hX hV hXV hε
  refine ⟨η,hη,?_⟩
  intro F hF hclose hmarks
  have hA : AnalyticOnNhd ℂ (F ∘ e.symm) V := by
    intro z hz
    exact (hF _ (mem_image_of_mem e.symm hz)).comp (hei z (hVe hz))
  have hB : ∀ z∈V, ‖(F ∘ e.symm) z-z‖≤η := by
    intro z hz
    simpa only [Function.comp_apply,e.right_inv (hVe hz)] using
      hclose _ (mem_image_of_mem e.symm hz)
  obtain ⟨E,hEs,hEi,hE,hout,hcomp,hsupp,hbound⟩ := Hη (F ∘ e.symm) hA hB
  exact ⟨E,hEs,hEi,hE,fun c hc => (hE c (hCX hc)).eq_of_nhds.trans (hmarks c hc),
    hout,hcomp,hsupp,hbound⟩

end FunctionTheory
