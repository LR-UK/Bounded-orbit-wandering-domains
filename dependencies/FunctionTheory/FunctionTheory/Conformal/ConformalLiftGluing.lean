import FunctionTheory.Analytic.Gluing
import FunctionTheory.Conformal.UnivalenceStability
import TauCeti.Analysis.Complex.Conformal.Inverse.Function

open Set Metric

namespace FunctionTheory

set_option autoImplicit false

/-- Gluing close holomorphic lifts yields a globally injective conformal
correction on any open set with enough room inside the covered neighbourhood.
The common collar controls injectivity between different charts. -/
theorem exists_glued_conformal_lift_with_collar
    {ι : Type*} {V W T : Set ℂ} (hV : IsOpen V) (hVW : V ⊆ W)
    (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = W)
    (θ : ι → ℂ → ℂ) (hθ : ∀ i, AnalyticOnNhd ℂ (θ i) (U i))
    {g φ : ℂ → ℂ} {r η : ℝ} (hr : 0 < r) (hη : 2 * η < r)
    (htube : ∀ z ∈ V, ball z r ⊆ W)
    (hnear : ∀ i, ∀ z ∈ U i, dist (θ i z) z < η)
    (hlift : ∀ i, ∀ z ∈ U i, g (θ i z) = φ z)
    (htarget : ∀ i, MapsTo (θ i) (U i) T)
    (hinj : ∀ i j, i ≠ j → ∀ z ∈ U i ∩ U j, InjOn g (ball z η)) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F W ∧ InjOn F V ∧ MapsTo F W T ∧
      DifferentiableOn ℂ (Function.invFunOn F V) (F '' V) ∧
      (∀ i, EqOn F (θ i) (U i)) ∧
      ∀ z ∈ W, dist (F z) z < η ∧ g (F z) = φ z := by
  obtain ⟨F, hFA, hFT, heq, hpair⟩ :=
    exists_glued_analytic_lift_of_injOn_overlaps U hU θ hθ hnear hlift htarget hinj
  rw [hcover] at hFA hFT hpair
  have hFi := injOn_of_close_to_id hr hη htube hFA.differentiableOn
    (fun z hz => (hpair z hz).1.le)
  exact ⟨F, hFA, hFi, hFT, (hFA.mono hVW).differentiableOn.invFunOn hV hFi, heq, hpair⟩

end FunctionTheory
