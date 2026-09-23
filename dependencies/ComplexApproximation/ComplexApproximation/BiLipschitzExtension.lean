import ComplexApproximation.HalfStripProjection
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FiniteDimensional
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Quantitative ambient extensions

A strict Lipschitz perturbation of the identity is a bi-Lipschitz plane
homeomorphism. Nonexpansive retractions allow the same construction on
closed half-strips, without a compactness hypothesis.
-/

open Set Metric Complex
open scoped NNReal

namespace ComplexApproximation

theorem exists_bilipschitz_homeomorph_of_lipschitz_error {g : ℂ → ℂ} {q : ℝ≥0}
    (hq : q < 1) (he : LipschitzWith q (fun z => g z - z)) :
    ∃ H : ℂ ≃ₜ ℂ, (∀ z, H z = g z) ∧
      LipschitzWith (1 + q) H ∧ LipschitzWith (1 - q)⁻¹ H.symm := by
  have happ : ApproximatesLinearOn g
      ((ContinuousLinearEquiv.refl ℝ ℂ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) univ q := by
    apply LipschitzOnWith.approximatesLinearOn
    exact he.lipschitzOnWith
  have hsmall : Subsingleton ℂ ∨ q <
      ‖((ContinuousLinearEquiv.refl ℝ ℂ).symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ := by
    right
    simpa using hq
  let H := happ.toHomeomorph g hsmall
  have hHeq (z : ℂ) : H z = g z := rfl
  have hanti : AntilipschitzWith (1 - q)⁻¹ g := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    simpa [Subtype.dist_eq]
      using (happ.antilipschitz hsmall).le_mul_dist (⟨x, mem_univ x⟩ : (univ : Set ℂ))
        (⟨y, mem_univ y⟩ : (univ : Set ℂ))
  refine ⟨H, hHeq, ?_, ?_⟩
  · have hl := LipschitzWith.id.add he
    convert hl using 1
    ext z
    simp only [hHeq, id_eq, add_sub_cancel]
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := hanti.le_mul_dist (H.symm x) (H.symm y)
    simpa only [← hHeq, H.apply_symm_apply] using h

theorem exists_bilipschitz_extension_of_retraction {S : Set ℂ} {P f : ℂ → ℂ}
    (hP : LipschitzWith 1 P) (hPS : MapsTo P univ S) (hfix : EqOn P id S)
    {q : ℝ≥0} (hq : q < 1) (hf : LipschitzOnWith q (fun z => f z - z) S) :
    ∃ H : ℂ ≃ₜ ℂ, EqOn f H S ∧
      LipschitzWith (1 + q) H ∧ LipschitzWith (1 - q)⁻¹ H.symm := by
  let g : ℂ → ℂ := fun z => z + (f (P z) - P z)
  have he : LipschitzWith q (fun z => g z - z) := by
    have hl : LipschitzWith (q * 1) (fun z => f (P z) - P z) :=
      lipschitzOnWith_univ.mp (hf.comp hP.lipschitzOnWith hPS)
    simpa only [g, add_sub_cancel_left, mul_one] using hl
  obtain ⟨H, hH, hl, hi⟩ := exists_bilipschitz_homeomorph_of_lipschitz_error hq he
  refine ⟨H, ?_, hl, hi⟩
  intro z hz
  rw [hH]
  change f z = z + (f (P z) - P z)
  rw [hfix hz]
  simp

theorem exists_bilipschitz_extension_of_small_error {S : Set ℂ} {f : ℂ → ℂ}
    {q : ℝ≥0} (hq : lipschitzExtensionConstant ℂ * q < 1)
    (hf : LipschitzOnWith q (fun z => f z - z) S) :
    ∃ H : ℂ ≃ₜ ℂ, EqOn f H S ∧ ∃ L L' : ℝ≥0,
      LipschitzWith L H ∧ LipschitzWith L' H.symm := by
  obtain ⟨u, hu, heq⟩ := hf.extend_finite_dimension
  let g : ℂ → ℂ := fun z => z + u z
  have he : LipschitzWith (lipschitzExtensionConstant ℂ * q) (fun z => g z - z) := by
    simpa only [g, add_sub_cancel_left] using hu
  obtain ⟨H, hH, hl, hi⟩ := exists_bilipschitz_homeomorph_of_lipschitz_error hq he
  refine ⟨H, ?_, _, _, hl, hi⟩
  intro z hz
  rw [hH]
  change f z = z + u z
  rw [← heq hz]
  simp

/-- The positive real part of a bounded derivative permits approximation by
a positive real scalar, with error strictly smaller than that scalar. -/
theorem exists_scalar_derivative_bound {m M : ℝ} (hm : 0 < m) :
    ∃ C c : ℝ, 0 < C ∧ 0 ≤ c ∧ c < C ∧
      ∀ d : ℂ, m ≤ d.re → ‖d‖ ≤ M → ‖d - (C : ℂ)‖ ≤ c := by
  let C := (M ^ 2 + 1) / m + m
  have hC : 0 < C := by dsimp [C]; positivity
  have hmC : m < C := by dsimp [C]; linarith [div_pos (by positivity : 0 < M ^ 2 + 1) hm]
  have hCm : C * m = M ^ 2 + 1 + m ^ 2 := by dsimp [C]; field_simp
  refine ⟨C, C - m / 2, hC, by linarith, by linarith, ?_⟩
  intro d hd hM
  have hM0 : 0 ≤ M := (norm_nonneg d).trans hM
  have hsq : ‖d - (C : ℂ)‖ ^ 2 = ‖d‖ ^ 2 - 2 * C * d.re + C ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hb : ‖d‖ ^ 2 ≤ M ^ 2 := (sq_le_sq₀ (norm_nonneg d) hM0).mpr hM
  have hmul := mul_le_mul_of_nonneg_left hd hC.le
  nlinarith [norm_nonneg (d - (C : ℂ))]

theorem exists_bilipschitz_extension_of_positive_derivative {S : Set ℂ} {P f : ℂ → ℂ}
    (hS : Convex ℝ S) (hP : LipschitzWith 1 P) (hPS : MapsTo P univ S)
    (hfix : EqOn P id S) (hf : ∀ z ∈ S, DifferentiableAt ℂ f z)
    {m M : ℝ} (hm : 0 < m)
    (hderiv : ∀ z ∈ S, m ≤ (deriv f z).re ∧ ‖deriv f z‖ ≤ M) :
    ∃ H : ℂ ≃ₜ ℂ, EqOn f H S ∧ ∃ L L' : ℝ≥0,
      LipschitzWith L H ∧ LipschitzWith L' H.symm := by
  obtain ⟨C, c, hC, hc, hcC, hbound⟩ := exists_scalar_derivative_bound (M := M) hm
  have hCne : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  let q : ℝ≥0 := ⟨c / C, div_nonneg hc hC.le⟩
  have hq : q < 1 := (div_lt_one hC).mpr hcC
  let g : ℂ → ℂ := fun z => (C : ℂ)⁻¹ * f z
  have herror : LipschitzOnWith q (fun z => g z - z) S := by
    apply hS.lipschitzOnWith_of_nnnorm_deriv_le
      (fun z hz => ((hf z hz).const_mul _).sub differentiableAt_id)
    intro z hz
    have hd := (((hf z hz).hasDerivAt.const_mul (C : ℂ)⁻¹).sub (hasDerivAt_id z)).deriv
    change deriv (fun w => (C : ℂ)⁻¹ * f w - w) z = (C : ℂ)⁻¹ * deriv f z - 1 at hd
    change ‖deriv (fun w => (C : ℂ)⁻¹ * f w - w) z‖ ≤ c / C
    rw [hd]
    have heq : (C : ℂ)⁻¹ * deriv f z - 1 = (C : ℂ)⁻¹ * (deriv f z - C) := by
      rw [mul_sub, inv_mul_cancel₀ hCne]
    rw [heq, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
    have hb := hbound (deriv f z) (hderiv z hz).1 (hderiv z hz).2
    simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hC.le)
  obtain ⟨H₀, heq, hl, hi⟩ := exists_bilipschitz_extension_of_retraction hP hPS hfix hq herror
  let H := H₀.trans (Homeomorph.mulLeft₀ (C : ℂ) hCne)
  have hH (z : ℂ) : H z = (C : ℂ) * H₀ z := rfl
  have hHi (z : ℂ) : H.symm z = H₀.symm ((C : ℂ)⁻¹ * z) := rfl
  have hmul (a : ℂ) : LipschitzWith ‖a‖₊ (fun z : ℂ => a * z) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simp only [dist_eq_norm, ← mul_sub, norm_mul, coe_nnnorm]
    exact le_rfl
  refine ⟨H, ?_, ‖(C : ℂ)‖₊ * (1 + q), (1 - q)⁻¹ * ‖(C : ℂ)⁻¹‖₊, ?_, ?_⟩
  · intro z hz
    rw [hH, ← heq hz]
    change f z = (C : ℂ) * ((C : ℂ)⁻¹ * f z)
    rw [← mul_assoc, mul_inv_cancel₀ hCne, one_mul]
  · exact (hmul C).comp hl
  · exact hi.comp (hmul (C : ℂ)⁻¹)

end ComplexApproximation
