import FunctionTheory.Smooth.NearIdentityHomeomorph
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Normed

open Set Filter
open scoped Topology ContDiff NNReal

namespace FunctionTheory

set_option autoImplicit false

/-- A smooth displacement with Lipschitz constant below one gives a global
smooth diffeomorphism of the plane, including smoothness of its inverse. -/
theorem exists_smooth_homeomorph_eq_add_of_lipschitz_lt_one
    {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u)
    {k : ℝ≥0} (hLip : LipschitzWith k u) (hk : k < 1) :
    ∃ e : ℂ ≃ₜ ℂ, (∀ x, e x = x + u x) ∧
      ContDiff ℝ ∞ (e : ℂ → ℂ) ∧ ContDiff ℝ ∞ (e.symm : ℂ → ℂ) := by
  classical
  obtain ⟨e, he⟩ := exists_homeomorph_eq_add_of_lipschitz_lt_one hLip hk
  let f : ℂ → ℂ := fun x => x + u x
  have heF : (e : ℂ → ℂ) = f := funext he
  have hf : ContDiff ℝ ∞ f := contDiff_id.add hu
  have hkR : (k : ℝ) < 1 := by exact_mod_cast hk
  refine ⟨e, he, by simpa only [heF] using hf, ?_⟩
  rw [contDiff_iff_contDiffAt]
  intro y
  let a := e.symm y
  have hfa : f a = y := by
    change f (e.symm y) = y
    rw [← heF]
    exact e.apply_symm_apply y
  have hsmall : ‖-(fderiv ℝ u a)‖ < 1 := by
    simpa only [norm_neg] using (norm_fderiv_le_of_lipschitz ℝ hLip (x₀ := a)).trans_lt hkR
  have hunit : IsUnit (1 + fderiv ℝ u a) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hsmall
  obtain ⟨v, hv⟩ := hunit
  let D : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.ofUnit v
  have hDf : HasFDerivAt f (D : ℂ →L[ℝ] ℂ) a := by
    change HasFDerivAt f (v : ℂ →L[ℝ] ℂ) a
    rw [hv]
    exact (hasFDerivAt_id a).add ((hu.differentiable (by simp)) a).hasFDerivAt
  have hfaSmooth : ContDiffAt ℝ ∞ f a := hf.contDiffAt
  let inv := hfaSmooth.localInverse hDf (by simp)
  have hInvSmooth : ContDiffAt ℝ ∞ inv (f a) := hfaSmooth.to_localInverse hDf (by simp)
  have hInvRight : ∀ᶠ z in 𝓝 (f a), f (inv z) = z :=
    (hfaSmooth.hasStrictFDerivAt' hDf (by simp)).eventually_right_inverse
  rw [hfa] at hInvSmooth hInvRight
  apply hInvSmooth.congr_of_eventuallyEq
  filter_upwards [hInvRight] with z hz
  apply e.injective
  rw [e.apply_symm_apply, he (inv z)]
  exact hz.symm

/-- Uniform derivative control supplies the Lipschitz hypothesis for a
smooth near-identity diffeomorphism. -/
theorem exists_smooth_homeomorph_eq_add_of_derivative_bound
    {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u) {k : ℝ≥0} (hk : k < 1)
    (hbound : ∀ z, ‖fderiv ℝ u z‖ ≤ k) :
    ∃ e : ℂ ≃ₜ ℂ, (∀ x, e x = x + u x) ∧
      ContDiff ℝ ∞ (e : ℂ → ℂ) ∧ ContDiff ℝ ∞ (e.symm : ℂ → ℂ) := by
  apply exists_smooth_homeomorph_eq_add_of_lipschitz_lt_one hu _ hk
  exact lipschitzWith_of_nnnorm_fderiv_le (hu.differentiable (by simp))
    (fun z => by exact_mod_cast hbound z)

end FunctionTheory
