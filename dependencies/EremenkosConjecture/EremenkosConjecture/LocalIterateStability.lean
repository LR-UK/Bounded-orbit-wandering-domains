import EremenkosConjecture.LocalArakelianStability
import EremenkosConjecture.IterateApproximation

open Set Metric Function
open scoped NNReal

namespace EremenkosConjecture

/-- Uniform finite-iterate approximation preserves the local chart on an
inset, up to a bi-Lipschitz change of image coordinates. -/
theorem approximate_local_iterate
    (g : ℂ → ℂ) (E : Set ℂ) (n : ℕ)
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he : EqOn (g^[n]) e e.source)
    (hei : DifferentiableOn ℂ e.symm e.target)
    (hcontrol : ∀ k < n, UniformControlOn g E ((g^[k]) '' e.source))
    {A : Set ℂ} (hA : A ⊆ e.source) {r : ℝ} (hr : 0 < r)
    (htube : ∀ z ∈ e '' A, ball z r ⊆ e.target)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℂ → ℂ, Differentiable ℂ f →
      (∀ z ∈ E, dist (f z) (g z) < δ) →
      (∃ H : ℂ ≃ₜ ℂ, EqOn (f^[n]) (H ∘ (g^[n])) A ∧
        ∃ L L' : ℝ≥0, LipschitzWith L H ∧ LipschitzWith L' H.symm) ∧
      (∀ k ≤ n, ∀ z ∈ e.source, dist ((f^[k]) z) ((g^[k]) z) < ε) ∧
      (∀ k < n, MapsTo (f^[k]) e.source E) := by
  obtain ⟨η, hη, Hη⟩ := exists_bilipschitz_image_tolerance e hei hA hr htube
  obtain ⟨δ, hδ, Hδ⟩ := iterate_approximation_of_uniform_control g E e.source n hcontrol
    (min ε η) (lt_min hε hη)
  refine ⟨δ, hδ, fun f hf hclose => ?_⟩
  obtain ⟨happrox, hdomain⟩ := Hδ f hclose
  obtain ⟨H, hH, hLip⟩ := Hη (f^[n]) (hf.iterate n).differentiableOn (by
    intro z hz
    rw [← he hz]
    exact ((happrox n le_rfl z hz).trans_le (min_le_right _ _)).le)
  refine ⟨⟨H, ?_, hLip⟩, ?_, hdomain⟩
  · intro z hz
    simpa only [comp_apply, he (hA hz)] using hH hz
  · intro k hk z hz
    exact (happrox k hk z hz).trans_le (min_le_left _ _)

end EremenkosConjecture
