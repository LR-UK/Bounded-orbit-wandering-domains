import EremenkosConjecture.Univalence
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FiniteDimensional

/-!
# Ambient homeomorphisms for small holomorphic perturbations

Schwarz's lemma makes the error of a small perturbation of the identity
Lipschitz on a compact set. Mathlib's finite-dimensional Lipschitz extension
theorem then extends the perturbed map to a homeomorphism of the plane.
Keeping this stronger property in the induction preserves fullness of images.
-/

open Set Metric Function
open scoped NNReal

namespace EremenkosConjecture

theorem lipschitzOnWith_sub_id_of_close {U A : Set ℂ} {r δ : ℝ} {c : ℝ≥0}
    (hr : 0 < r) (hδ : 2 * δ ≤ c * r) (htube : ∀ x ∈ A, ball x r ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hclose : ∀ z ∈ U, dist (f z) z ≤ δ) :
    LipschitzOnWith c (fun z => f z - z) A := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hxU : x ∈ U := htube x hx (mem_ball_self hr)
  have hyU : y ∈ U := htube y hy (mem_ball_self hr)
  let e : ℂ → ℂ := fun z => f z - z
  have he : DifferentiableOn ℂ e U := hf.sub differentiableOn_id
  have hbound : ∀ v ∈ U, ∀ w ∈ U, dist (e v) (e w) ≤ 2 * δ := by
    intro v hv w hw
    rw [dist_eq_norm]
    calc
      ‖e v - e w‖ ≤ ‖e v‖ + ‖e w‖ := norm_sub_le _ _
      _ ≤ δ + δ := add_le_add (by simpa [e, dist_eq_norm] using hclose v hv)
        (by simpa [e, dist_eq_norm] using hclose w hw)
      _ = 2 * δ := by ring
  by_cases hnear : dist x y < r
  · have hmaps : MapsTo e (ball y r) (closedBall (e y) (2 * δ)) :=
      fun w hw => hbound w (htube y hy hw) y hyU
    have H := Complex.dist_le_div_mul_dist_of_mapsTo_ball (he.mono (htube y hy)) hmaps hnear
    exact H.trans (mul_le_mul_of_nonneg_right ((div_le_iff₀ hr).mpr hδ) dist_nonneg)
  · exact (hbound x hxU y hyU).trans (hδ.trans
      (mul_le_mul_of_nonneg_left (le_of_not_gt hnear) c.coe_nonneg))

theorem exists_homeomorph_tolerance_near_id (U A : Set ℂ) (hU : IsOpen U)
    (hA : IsCompact A) (hAU : A ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
      (∀ z ∈ U, dist (f z) z ≤ δ) → ∃ H : ℂ ≃ₜ ℂ, EqOn f H A := by
  obtain ⟨r, hr, htube⟩ := hA.exists_thickening_subset_open hU hAU
  let C : ℝ≥0 := lipschitzExtensionConstant ℂ
  have hC : 0 < C := lipschitzExtensionConstant_pos ℂ
  let c : ℝ≥0 := (2 * C)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨(c : ℝ) * r / 2, by positivity, fun f hf hclose => ?_⟩
  have hsmall : LipschitzOnWith c (fun z => f z - z) A :=
    lipschitzOnWith_sub_id_of_close hr (by ring_nf; rfl)
      (fun x hx y hy => htube (mem_thickening_iff.mpr ⟨x, hx, hy⟩)) hf hclose
  have happ : ApproximatesLinearOn f
      ((ContinuousLinearEquiv.refl ℝ ℂ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) A c := by
    apply LipschitzOnWith.approximatesLinearOn
    change LipschitzOnWith c (fun z => f z - z) A
    exact hsmall
  apply happ.exists_homeomorph_extension
  right
  change C * c < ‖ContinuousLinearMap.id ℝ ℂ‖₊⁻¹
  rw [ContinuousLinearMap.nnnorm_id, inv_one]
  change C * (2 * C)⁻¹ < 1
  rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hC), one_mul]
  norm_num

/-- Compact stability preserving an extension to a homeomorphism of the whole
plane. This stronger conclusion makes fullness of images available in the
recursive approximation construction. -/
theorem exists_homeomorph_approximation_tolerance
    (e : OpenPartialHomeomorph ℂ ℂ) (hei : DifferentiableOn ℂ e.symm e.target)
    (H : ℂ ≃ₜ ℂ) (heH : EqOn e H e.source)
    (A : Set ℂ) (hA : IsCompact A) (hAU : A ⊆ e.source) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f e.source →
      (∀ z ∈ e.source, dist (f z) (e z) ≤ δ) →
      ∃ G : ℂ ≃ₜ ℂ, EqOn f G A := by
  have hAc : IsCompact (e '' A) := hA.image_of_continuousOn (e.continuousOn.mono hAU)
  have hAV : e '' A ⊆ e.target := e.mapsTo.image_subset.trans' (image_mono hAU)
  obtain ⟨δ, hδ, Hδ⟩ := exists_homeomorph_tolerance_near_id e.target (e '' A)
    e.open_target hAc hAV
  refine ⟨δ, hδ, fun f hf hclose => ?_⟩
  have hcomp : DifferentiableOn ℂ (f ∘ e.symm) e.target := hf.comp hei e.mapsTo_symm
  have happrox : ∀ z ∈ e.target, dist ((f ∘ e.symm) z) z ≤ δ := by
    intro z hz
    simpa only [Function.comp_apply, e.right_inv hz] using hclose (e.symm z) (e.map_target hz)
  obtain ⟨G, hG⟩ := Hδ (f ∘ e.symm) hcomp happrox
  refine ⟨H.trans G, fun z hz => ?_⟩
  calc
    f z = (f ∘ e.symm) (e z) := by rw [Function.comp_apply, e.left_inv (hAU hz)]
    _ = G (e z) := hG (mem_image_of_mem e hz)
    _ = (H.trans G) z := by rw [heH (hAU hz)]; rfl

theorem isConnected_compl_image_homeomorph (H : ℂ ≃ₜ ℂ) {K : Set ℂ}
    (hK : IsConnected Kᶜ) : IsConnected (H '' K)ᶜ := by
  have h := hK.image H H.continuous.continuousOn
  change IsConnected (H.toEquiv '' Kᶜ) at h
  rwa [H.toEquiv.image_compl] at h

end EremenkosConjecture
