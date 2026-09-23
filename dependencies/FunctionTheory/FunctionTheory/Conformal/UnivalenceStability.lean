import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Tactic.Linarith

/-!
# Stability of univalent maps

Moved unchanged, apart from the namespace, from the EremenkosConjecture
project so other applications can reuse these classical estimates. The original
module retains compatibility aliases.

The elementary near-identity estimate uses Schwarz's lemma on a ball around
each point. Conjugating by a conformal inverse gives stability on a compact
subset, without needing a quantitative global distortion theorem.
-/

open Set Metric Function

namespace FunctionTheory

/-- A holomorphic map uniformly close to the identity is injective on any
set with a sufficiently large uniform margin inside its domain. -/
theorem injOn_of_close_to_id {U A : Set ℂ} {r δ : ℝ} (hr : 0 < r)
    (hδ : 2 * δ < r) (htube : ∀ x ∈ A, ball x r ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hclose : ∀ z ∈ U, dist (f z) z ≤ δ) : InjOn f A := by
  intro x hx y hy hxy
  by_contra hne
  have hxU : x ∈ U := htube x hx (mem_ball_self hr)
  have hyU : y ∈ U := htube y hy (mem_ball_self hr)
  let e : ℂ → ℂ := fun z => f z - z
  have he : DifferentiableOn ℂ e U := hf.sub differentiableOn_id
  have he_dist : dist (e y) (e x) = dist y x := by
    rw [dist_eq_norm, dist_eq_norm]
    have heq : e y - e x = -(y - x) := by simp only [e, hxy]; ring
    rw [heq, norm_neg]
  have hyx : 0 < dist y x := dist_pos.mpr (Ne.symm hne)
  by_cases hnear : dist y x < r
  · have hmaps : MapsTo e (ball x r) (closedBall (e x) (2 * δ)) := by
      intro z hz
      rw [mem_closedBall, dist_eq_norm]
      calc
        ‖e z - e x‖ ≤ ‖e z‖ + ‖e x‖ := norm_sub_le _ _
        _ ≤ δ + δ := add_le_add (by simpa [e, dist_eq_norm] using hclose z (htube x hx hz))
          (by simpa [e, dist_eq_norm] using hclose x hxU)
        _ = 2 * δ := by ring
    have hbound := Complex.dist_le_div_mul_dist_of_mapsTo_ball
      (he.mono (htube x hx)) hmaps hnear
    rw [he_dist] at hbound
    have hratio : 2 * δ / r < 1 := (div_lt_one hr).mpr hδ
    nlinarith
  · have hbound : dist y x ≤ 2 * δ := by
      calc
        dist y x ≤ dist y (f y) + dist (f y) x := dist_triangle _ _ _
        _ ≤ δ + δ := add_le_add (by simpa [dist_comm] using hclose y hyU)
          (by simpa [hxy] using hclose x hxU)
        _ = 2 * δ := by ring
    exact hnear (hbound.trans_lt hδ)

theorem mapsTo_of_close_to_id {U A : Set ℂ} {r δ : ℝ}
    (hδ : δ < r) (hAU : A ⊆ U) (htube : ∀ x ∈ A, ball x r ⊆ U)
    {f : ℂ → ℂ} (hclose : ∀ z ∈ U, dist (f z) z ≤ δ) : MapsTo f A U := by
  intro z hz
  exact htube z hz ((hclose z (hAU hz)).trans_lt hδ)

/-- Compact univalence stability for a conformal isomorphism. The inverse is
holomorphic on the target, and the approximation is only required on the source. -/
theorem exists_injective_approximation_tolerance
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he : DifferentiableOn ℂ e.symm e.target)
    (A : Set ℂ) (hA : IsCompact A) (hAU : A ⊆ e.source) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f e.source →
      (∀ z ∈ e.source, dist (f z) (e z) ≤ δ) →
      InjOn f A ∧ MapsTo f A e.target := by
  have himage : IsCompact (e '' A) := hA.image_of_continuousOn (e.continuousOn.mono hAU)
  have hAV : e '' A ⊆ e.target := e.mapsTo.image_subset.trans' (image_mono hAU)
  obtain ⟨r, hr, htube⟩ := himage.exists_thickening_subset_open e.open_target hAV
  have hballs : ∀ x ∈ e '' A, ball x r ⊆ e.target := by
    intro x hx y hy
    exact htube (mem_thickening_iff.mpr ⟨x, hx, hy⟩)
  refine ⟨r / 4, by positivity, fun f hf hclose => ?_⟩
  have hcomp : DifferentiableOn ℂ (f ∘ e.symm) e.target := hf.comp he e.mapsTo_symm
  have happrox : ∀ z ∈ e.target, dist ((f ∘ e.symm) z) z ≤ r / 4 := by
    intro z hz
    simpa only [Function.comp_apply, e.right_inv hz] using hclose (e.symm z) (e.map_target hz)
  have hinj := injOn_of_close_to_id hr (show 2 * (r / 4) < r by linarith)
    hballs hcomp happrox
  have hmap := mapsTo_of_close_to_id (show r / 4 < r by linarith) hAV hballs happrox
  constructor
  · intro x hx y hy hxy
    apply e.injOn (hAU hx) (hAU hy)
    apply hinj (mem_image_of_mem e hx) (mem_image_of_mem e hy)
    simpa only [Function.comp_apply, e.left_inv (hAU hx), e.left_inv (hAU hy)] using hxy
  · intro z hz
    simpa only [Function.comp_apply, e.left_inv (hAU hz)] using hmap (mem_image_of_mem e hz)

/-- Uniform approximation controls derivatives on every compact subset of the
open domain. The reference and approximating functions need only be holomorphic. -/
theorem exists_derivative_approximation_tolerance (U A : Set ℂ)
    (hU : IsOpen U) (hA : IsCompact A) (hAU : A ⊆ U) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f g : ℂ → ℂ,
      DifferentiableOn ℂ f U → DifferentiableOn ℂ g U →
      (∀ z ∈ U, dist (f z) (g z) ≤ δ) →
      ∀ z ∈ A, ‖deriv f z - deriv g z‖ < η := by
  obtain ⟨r, hr, htube⟩ := hA.exists_thickening_subset_open hU hAU
  refine ⟨η * r / 4, by positivity, fun f g hf hg hclose z hz => ?_⟩
  have hball : ball z r ⊆ U := fun w hw => htube (mem_thickening_iff.mpr ⟨z, hz, hw⟩)
  let d : ℂ → ℂ := fun w => f w - g w
  have hd : DifferentiableOn ℂ d U := hf.sub hg
  have hmaps : MapsTo d (ball z r) (closedBall (d z) (2 * (η * r / 4))) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm]
    calc
      ‖d w - d z‖ ≤ ‖d w‖ + ‖d z‖ := norm_sub_le _ _
      _ ≤ η * r / 4 + η * r / 4 := add_le_add
        (by simpa [d, dist_eq_norm] using hclose w (hball hw))
        (by simpa [d, dist_eq_norm] using hclose z (hAU hz))
      _ = 2 * (η * r / 4) := by ring
  have hbound := Complex.norm_deriv_le_div_of_mapsTo_ball (hd.mono hball) hmaps hr
  have hderiv : deriv d z = deriv f z - deriv g z :=
    ((hf.differentiableAt (hU.mem_nhds (hAU hz))).hasDerivAt.sub
      (hg.differentiableAt (hU.mem_nhds (hAU hz))).hasDerivAt).deriv
  rw [hderiv] at hbound
  have hval : 2 * (η * r / 4) / r = η / 2 := by field_simp; ring
  rw [hval] at hbound
  exact hbound.trans_lt (half_lt_self hη)

/-- Compact-set form of Lemma 2.3, including derivative control. The lower
bound `η` may be any positive lower bound for the reference derivative. -/
theorem approximation_of_univalent_on_compact (e : OpenPartialHomeomorph ℂ ℂ)
    (he : DifferentiableOn ℂ e e.source) (hei : DifferentiableOn ℂ e.symm e.target)
    (A : Set ℂ) (hA : IsCompact A) (hAU : A ⊆ e.source)
    (η : ℝ) (hη : 0 < η) (hderiv : ∀ z ∈ A, η ≤ ‖deriv e z‖) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f e.source →
      (∀ z ∈ e.source, dist (f z) (e z) ≤ δ) →
      InjOn f A ∧ MapsTo f A e.target ∧
      ∀ z ∈ A, ‖deriv f z - deriv e z‖ < η / 2 ∧ η / 2 < ‖deriv f z‖ := by
  obtain ⟨δ₁, hδ₁, H₁⟩ := exists_injective_approximation_tolerance e hei A hA hAU
  obtain ⟨δ₂, hδ₂, H₂⟩ := exists_derivative_approximation_tolerance e.source A
    e.open_source hA hAU (η / 2) (half_pos hη)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun f hf hclose => ?_⟩
  obtain ⟨hinj, hmap⟩ := H₁ f hf (fun z hz => (hclose z hz).trans (min_le_left _ _))
  refine ⟨hinj, hmap, fun z hz => ?_⟩
  have hdiff := H₂ f e hf he (fun z hz => (hclose z hz).trans (min_le_right _ _)) z hz
  refine ⟨hdiff, ?_⟩
  have hnorm := norm_sub_norm_le (deriv e z) (deriv f z)
  rw [norm_sub_rev] at hnorm
  have hlo := hderiv z hz
  linarith

end FunctionTheory
