import EremenkosConjecture.UniformAmbientExtension
import ComplexApproximation.Topology.ArakelianHomeomorphism

open Set Metric Function
open scoped NNReal

namespace EremenkosConjecture

/-- A sufficiently close holomorphic perturbation of a conformal chart has,
on the prescribed inset, image related to the old image by a plane homeomorphism.
There is no extension assumption on the reference chart. -/
theorem exists_bilipschitz_image_tolerance
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he : DifferentiableOn ℂ e.symm e.target)
    {A : Set ℂ} (hA : A ⊆ e.source) {r : ℝ} (hr : 0 < r)
    (htube : ∀ z ∈ e '' A, ball z r ⊆ e.target) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f e.source →
      (∀ z ∈ e.source, dist (f z) (e z) ≤ δ) →
      ∃ H : ℂ ≃ₜ ℂ, EqOn f (H ∘ e) A ∧ ∃ L L' : ℝ≥0,
        LipschitzWith L H ∧ LipschitzWith L' H.symm := by
  obtain ⟨δ, hδ, Hδ⟩ := exists_bilipschitz_tolerance_near_id hr htube
  refine ⟨δ, hδ, fun f hf hclose => ?_⟩
  have hcomp : DifferentiableOn ℂ (f ∘ e.symm) e.target := hf.comp he e.mapsTo_symm
  have hc : ∀ z ∈ e.target, dist ((f ∘ e.symm) z) z ≤ δ := by
    intro z hz
    simpa only [Function.comp_apply, e.right_inv hz] using
      hclose (e.symm z) (e.map_target hz)
  obtain ⟨H, hH, hLip⟩ := Hδ (f ∘ e.symm) hcomp hc
  refine ⟨H, fun z hz => ?_, hLip⟩
  simpa only [Function.comp_apply, e.left_inv (hA hz)] using
    hH (mem_image_of_mem e hz)

theorem exists_image_homeomorph_tolerance
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he : DifferentiableOn ℂ e.symm e.target)
    {A : Set ℂ} (hA : A ⊆ e.source) {r : ℝ} (hr : 0 < r)
    (htube : ∀ z ∈ e '' A, ball z r ⊆ e.target) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f e.source →
      (∀ z ∈ e.source, dist (f z) (e z) ≤ δ) →
      ∃ H : ℂ ≃ₜ ℂ, EqOn f (H ∘ e) A := by
  obtain ⟨δ, hδ, Hδ⟩ := exists_bilipschitz_image_tolerance e he hA hr htube
  exact ⟨δ, hδ, fun f hf hc => by
    obtain ⟨H, hH, _⟩ := Hδ f hf hc
    exact ⟨H, hH⟩⟩

/-- The Arakelian property of the image is stable under sufficiently close
holomorphic perturbations, using a target tube instead of an ambient extension. -/
theorem exists_arakelian_image_tolerance
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he : DifferentiableOn ℂ e.symm e.target)
    {A : Set ℂ} (hA : A ⊆ e.source) {r : ℝ} (hr : 0 < r)
    (htube : ∀ z ∈ e '' A, ball z r ⊆ e.target)
    (himage : ComplexApproximation.IsArakelian (e '' A)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f e.source →
      (∀ z ∈ e.source, dist (f z) (e z) ≤ δ) →
      ComplexApproximation.IsArakelian (f '' A) := by
  obtain ⟨δ, hδ, Hδ⟩ := exists_image_homeomorph_tolerance e he hA hr htube
  refine ⟨δ, hδ, fun f hf hc => ?_⟩
  obtain ⟨H, hH⟩ := Hδ f hf hc
  have heq : f '' A = H '' (e '' A) := by
    rw [image_image]
    exact image_congr hH
  rw [heq]
  exact himage.image_homeomorph H

end EremenkosConjecture
