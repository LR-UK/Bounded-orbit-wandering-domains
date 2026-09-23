import Runge.SmoothCutoff
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.Ring

/-!
# The Cauchy–Riemann defect and the Cauchy–Green kernel

The normalization used here is `I * ∂ₓg - ∂ᵧg`, matching Mathlib's
rectangle form of Green's theorem.
-/

open Complex Set Function Filter MeasureTheory
open scoped Topology ContDiff

namespace Runge

noncomputable def cauchyRiemannDefect (g : ℂ → ℂ) (w : ℂ) : ℂ :=
  I * fderiv ℝ g w 1 - fderiv ℝ g w I

theorem cauchyRiemannDefect_eq_zero {g : ℂ → ℂ} {w : ℂ}
    (hg : DifferentiableAt ℂ g w) : cauchyRiemannDefect g w = 0 := by
  rw [cauchyRiemannDefect, hg.fderiv_restrictScalars ℝ]
  change I * (fderiv ℂ g w) 1 - (fderiv ℂ g w) I = 0
  have h := (fderiv ℂ g w).map_smul I (1 : ℂ)
  simpa only [smul_eq_mul, mul_one, sub_eq_zero] using h.symm

theorem continuous_cauchyRiemannDefect {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g) :
    Continuous (cauchyRiemannDefect g) := by
  have h := hg.continuous_fderiv_apply (by simp)
  exact (continuous_const.mul (h.comp (continuous_id.prodMk continuous_const))).sub
    (h.comp (continuous_id.prodMk continuous_const))

theorem hasCompactSupport_cauchyRiemannDefect {g : ℂ → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport (cauchyRiemannDefect g) := by
  exact (hg.fderiv_apply ℝ 1).mul_left.sub (hg.fderiv_apply ℝ I)

theorem cauchyRiemannDefect_congr {g f : ℂ → ℂ} {w : ℂ}
    (h : g =ᶠ[𝓝 w] f) : cauchyRiemannDefect g w = cauchyRiemannDefect f w := by
  simp only [cauchyRiemannDefect, h.fderiv_eq]

theorem cauchyRiemannDefect_mul {g h : ℂ → ℂ} {w : ℂ}
    (hg : DifferentiableAt ℝ g w) (hh : DifferentiableAt ℂ h w) :
    cauchyRiemannDefect (fun z => h z * g z) w = h w * cauchyRiemannDefect g w := by
  have hzero := cauchyRiemannDefect_eq_zero hh
  simp only [cauchyRiemannDefect] at hzero ⊢
  rw [fderiv_fun_mul (hh.restrictScalars ℝ) hg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [← sub_eq_zero.mp hzero]
  ring

theorem cauchyRiemannDefect_sub_const {g : ℂ → ℂ} (w a : ℂ) :
    cauchyRiemannDefect (fun z => g z - a) w = cauchyRiemannDefect g w := by
  simp only [cauchyRiemannDefect, fderiv_sub_const]

theorem cauchyRiemannDefect_dslope {g : ℂ → ℂ} {z w : ℂ}
    (hg : DifferentiableAt ℝ g w) (hw : w ≠ z) :
    cauchyRiemannDefect (dslope g z) w = cauchyRiemannDefect g w / (w - z) := by
  have hh : DifferentiableAt ℂ (fun u : ℂ => (u - z)⁻¹) w :=
    (differentiableAt_id.sub_const z).inv (sub_ne_zero.mpr hw)
  rw [cauchyRiemannDefect_congr (dslope_eventuallyEq_slope_of_ne g hw)]
  change cauchyRiemannDefect (fun u => (u-z)⁻¹ * (g u-g z)) w = _
  rw [cauchyRiemannDefect_mul (hg.sub_const _) hh, cauchyRiemannDefect_sub_const]
  exact (div_eq_inv_mul _ _).symm

/-- The smooth extension has its Cauchy–Riemann defect supported away from `K`.
This is the separation needed for uniform approximation of its Cauchy integral. -/
theorem exists_extension_with_separated_defect (K U : Set ℂ) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) :
    ∃ g : ℂ → ℂ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∀ x ∈ K, g =ᶠ[𝓝 x] f) ∧ Disjoint (tsupport (cauchyRiemannDefect g)) K := by
  obtain ⟨g, hg, hgc, hgf⟩ := exists_smooth_compact_extension K U hK hU hKU f hf
  refine ⟨g, hg, hgc, hgf, Set.disjoint_right.mpr ?_⟩
  intro x hx
  rw [notMem_tsupport_iff_eventuallyEq]
  have he := (hgf x hx).eventuallyEq_nhds
  filter_upwards [he, hU.mem_nhds (hKU hx)] with y hy hyU
  exact (cauchyRiemannDefect_congr hy).trans (cauchyRiemannDefect_eq_zero (hf y hyU).differentiableAt)

/-- The positively oriented integral over the four sides of a rectangle. -/
noncomputable def rectangleBoundary (F : ℂ → ℂ) (a b : ℂ) : ℂ :=
  (∫ x : ℝ in a.re..b.re, F (x + a.im * I)) -
    (∫ x : ℝ in a.re..b.re, F (x + b.im * I)) +
    I * (∫ y : ℝ in a.im..b.im, F (b.re + y * I)) -
    I * (∫ y : ℝ in a.im..b.im, F (a.re + y * I))

/-- Green's theorem applied to the difference quotient with its removable
singularity filled in. The defect is precisely the Cauchy kernel. -/
theorem rectangleBoundary_dslope (g : ℂ → ℂ) (hc : Continuous g)
    (hd : Differentiable ℝ g) (z a b : ℂ) (hz : DifferentiableAt ℂ g z)
    (hi : IntegrableOn (fun w => cauchyRiemannDefect g w / (w-z))
      (Set.uIcc a.re b.re ×ℂ Set.uIcc a.im b.im)) :
    rectangleBoundary (dslope g z) a b =
      ∫ x : ℝ in a.re..b.re, ∫ y : ℝ in a.im..b.im,
        cauchyRiemannDefect g (x + y * I) / (x + y * I - z) := by
  classical
  let D : ℂ → ℂ →L[ℝ] ℂ :=
    fun w => if w = z then 0 else fderiv ℝ (dslope g z) w
  have hD (w : ℂ) : I • D w 1 - D w I = cauchyRiemannDefect g w / (w-z) := by
    by_cases hw : w = z
    · subst w
      simp [D]
    · simpa only [D, ite_eq_right hw, smul_eq_mul, cauchyRiemannDefect] using
        cauchyRiemannDefect_dslope (hd w) hw
  have hdc : Continuous (dslope g z) := by
    rw [← continuousOn_univ, continuousOn_dslope (by simp)]
    exact ⟨hc.continuousOn, hz⟩
  have hdd (w : ℂ) (hw : w ≠ z) : HasFDerivAt (dslope g z) (D w) w := by
    have hh : DifferentiableAt ℂ (fun u : ℂ => (u-z)⁻¹) w :=
      (differentiableAt_id.sub_const z).inv (sub_ne_zero.mpr hw)
    have hdiff : DifferentiableAt ℝ (dslope g z) w :=
      ((hh.restrictScalars ℝ).smul ((hd w).sub_const (g z))).congr_of_eventuallyEq
        (dslope_eventuallyEq_slope_of_ne g hw)
    simpa only [D, ite_eq_right hw] using hdiff.hasFDerivAt
  have H := Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable
    (dslope g z) D a b {z} (Set.countable_singleton z) hdc.continuousOn
    (fun w hw => hdd w (by simpa only [Set.mem_singleton_iff] using hw.2))
    (by simpa only [hD] using hi)
  simp_rw [hD] at H
  simpa only [rectangleBoundary, smul_eq_mul] using H

end Runge
