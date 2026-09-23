import EremenkosConjecture.UniformUnivalence
import EremenkosConjecture.IterateApproximation
import Mathlib.Analysis.Calculus.MeanValue

/-! # Uniform stability on possibly unbounded sets

The image and source margins are explicit. Compactness is not assumed.
These statements isolate the quantitative hypotheses needed by Section 7.
-/

open Set Metric Function

namespace EremenkosConjecture

theorem uniformControlOn_of_derivative_bound {U A : Set ℂ} {r C : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C) (htube : ∀ z ∈ A, ball z r ⊆ U)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U)
    (hderiv : ∀ z ∈ U, ‖deriv g z‖ ≤ C) : UniformControlOn g U A := by
  intro ε hε
  refine ⟨min r (ε / (C + 1)), lt_min hr (div_pos hε (by linarith)), ?_⟩
  intro x hx y hy
  have hyr : dist y x < r := hy.trans_le (min_le_left _ _)
  have hyε : dist y x < ε / (C + 1) := hy.trans_le (min_le_right _ _)
  refine ⟨htube x hx hyr, ?_⟩
  have hb : ball x r ⊆ U := htube x hx
  have hdiff : ∀ z ∈ ball x r, DifferentiableAt ℂ g z := fun z hz =>
    (hg.mono hb).differentiableAt (isOpen_ball.mem_nhds hz)
  have H := (convex_ball x r).norm_image_sub_le_of_norm_deriv_le hdiff
    (fun z hz => hderiv z (hb hz)) (mem_ball_self hr) hyr
  rw [dist_eq_norm] at hyr hyε ⊢
  have he : (C + 1) * ‖y - x‖ < ε := by
    have := (lt_div_iff₀ (by linarith : 0 < C + 1)).mp hyε
    nlinarith
  exact H.trans_lt (by nlinarith [norm_nonneg (y - x)])

/-- A uniform margin around the image replaces the compactness hypothesis
in the basic conformal stability lemma. -/
theorem injective_approximation_of_target_tube
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he : DifferentiableOn ℂ e.symm e.target) {A : Set ℂ} (hA : A ⊆ e.source)
    {r δ : ℝ} (hr : 0 < r) (hδ : 2 * δ < r)
    (htube : ∀ z ∈ e '' A, ball z r ⊆ e.target)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f e.source)
    (hclose : ∀ z ∈ e.source, dist (f z) (e z) ≤ δ) :
    InjOn f A ∧ MapsTo f A e.target := by
  have hcomp : DifferentiableOn ℂ (f ∘ e.symm) e.target := hf.comp he e.mapsTo_symm
  have happrox : ∀ z ∈ e.target, dist ((f ∘ e.symm) z) z ≤ δ := by
    intro z hz
    simpa only [Function.comp_apply, e.right_inv hz] using hclose (e.symm z) (e.map_target hz)
  have hinj := injOn_of_close_to_id hr hδ htube hcomp happrox
  have hδr : δ < r := by linarith
  have hmap := mapsTo_of_close_to_id hδr
    (show e '' A ⊆ e.target from fun _ ⟨z, hz, hez⟩ => hez ▸ e.map_source (hA hz))
    htube happrox
  constructor
  · intro x hx y hy hxy
    apply e.injOn (hA hx) (hA hy)
    apply hinj (mem_image_of_mem e hx) (mem_image_of_mem e hy)
    simpa only [Function.comp_apply, e.left_inv (hA hx), e.left_inv (hA hy)] using hxy
  · intro z hz
    simpa only [Function.comp_apply, e.left_inv (hA hz)] using hmap (mem_image_of_mem e hz)

theorem derivative_bounds_of_uniform_approximation {U A : Set ℂ} {r δ c C : ℝ}
    (hr : 0 < r) (htube : ∀ z ∈ A, ball z r ⊆ U)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hclose : ∀ z ∈ U, ‖f z - g z‖ ≤ δ)
    (hbound : ∀ z ∈ A, c ≤ ‖deriv g z‖ ∧ ‖deriv g z‖ ≤ C) :
    ∀ z ∈ A, c - 2 * δ / r ≤ ‖deriv f z‖ ∧ ‖deriv f z‖ ≤ C + 2 * δ / r := by
  intro z hz
  have hdiff := norm_deriv_sub_le_of_close_on_ball hr (hf.mono (htube z hz))
    (hg.mono (htube z hz)) (fun w hw => hclose w (htube z hz hw))
  have hlo := norm_sub_norm_le (deriv g z) (deriv f z)
  have hhi := norm_sub_norm_le (deriv f z) (deriv g z)
  rw [norm_sub_rev] at hlo
  obtain ⟨hl, hu⟩ := hbound z hz
  constructor <;> linarith

end EremenkosConjecture
