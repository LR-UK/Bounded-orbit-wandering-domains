import EremenkosConjecture.AmbientExtension
import EremenkosConjecture.UniformConformalStability
import ComplexApproximation.BiLipschitzExtension

/-! # Ambient stability on unbounded sets with a uniform margin -/

open Set Metric Function
open scoped NNReal

namespace EremenkosConjecture

theorem exists_uniform_image_tube (H : ℂ ≃ₜ ℂ) {L : ℝ≥0}
    (hL : LipschitzWith L H.symm) {A U : Set ℂ} {r : ℝ}
    (hr : 0 < r) (htube : ∀ z ∈ A, ball z r ⊆ U) :
    ∃ s : ℝ, 0 < s ∧ ∀ w ∈ H '' A, ball w s ⊆ H '' U := by
  refine ⟨r / (L + 1), div_pos hr (by positivity), ?_⟩
  rintro w ⟨z, hz, rfl⟩ y hy
  refine ⟨H.symm y, htube z hz ?_, H.apply_symm_apply y⟩
  have hb := hL.dist_le_mul y (H z)
  rw [H.symm_apply_apply] at hb
  have hy' : dist y (H z) * (L + 1) < r := (lt_div_iff₀ (by positivity)).mp hy
  exact hb.trans_lt (by nlinarith [dist_nonneg (x := y) (y := H z)])

theorem exists_bilipschitz_tolerance_near_id {U A : Set ℂ} {r : ℝ}
    (hr : 0 < r) (htube : ∀ z ∈ A, ball z r ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
      (∀ z ∈ U, dist (f z) z ≤ δ) →
      ∃ H : ℂ ≃ₜ ℂ, EqOn f H A ∧ ∃ L L' : ℝ≥0,
        LipschitzWith L H ∧ LipschitzWith L' H.symm := by
  let C : ℝ≥0 := lipschitzExtensionConstant ℂ
  have hC : 0 < C := lipschitzExtensionConstant_pos ℂ
  let c : ℝ≥0 := (2 * C)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have hsmall : lipschitzExtensionConstant ℂ * c < 1 := by
    change C * (2 * C)⁻¹ < 1
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hC), one_mul]
    norm_num
  refine ⟨(c : ℝ) * r / 2, by positivity, fun f hf hclose => ?_⟩
  exact ComplexApproximation.exists_bilipschitz_extension_of_small_error hsmall
    (lipschitzOnWith_sub_id_of_close hr (by ring_nf; rfl) htube hf hclose)

/-- An explicit target tube replaces compactness in ambient stability. -/
theorem exists_bilipschitz_approximation_tolerance
    (e : OpenPartialHomeomorph ℂ ℂ) (hei : DifferentiableOn ℂ e.symm e.target)
    (H : ℂ ≃ₜ ℂ) (heH : EqOn e H e.source) {L L' : ℝ≥0}
    (hL : LipschitzWith L H) (hL' : LipschitzWith L' H.symm)
    {A : Set ℂ} (hA : A ⊆ e.source) {r : ℝ} (hr : 0 < r)
    (htube : ∀ z ∈ e '' A, ball z r ⊆ e.target) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f e.source →
      (∀ z ∈ e.source, dist (f z) (e z) ≤ δ) →
      ∃ G : ℂ ≃ₜ ℂ, EqOn f G A ∧ ∃ M M' : ℝ≥0,
        LipschitzWith M G ∧ LipschitzWith M' G.symm := by
  obtain ⟨δ, hδ, Hδ⟩ := exists_bilipschitz_tolerance_near_id hr htube
  refine ⟨δ, hδ, fun f hf hclose => ?_⟩
  have hcomp : DifferentiableOn ℂ (f ∘ e.symm) e.target := hf.comp hei e.mapsTo_symm
  have happrox : ∀ z ∈ e.target, dist ((f ∘ e.symm) z) z ≤ δ := by
    intro z hz
    simpa only [Function.comp_apply, e.right_inv hz] using hclose (e.symm z) (e.map_target hz)
  obtain ⟨G, hG, M, M', hM, hM'⟩ := Hδ (f ∘ e.symm) hcomp happrox
  refine ⟨H.trans G, ?_, M * L, L' * M', hM.comp hL, hL'.comp hM'⟩
  intro z hz
  calc
    f z = (f ∘ e.symm) (e z) := by rw [Function.comp_apply, e.left_inv (hA hz)]
    _ = G (e z) := hG (mem_image_of_mem e hz)
    _ = (H.trans G) z := by rw [heH (hA hz)]; rfl

end EremenkosConjecture
