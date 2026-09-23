import ComplexApproximation.CauchyTransform
import ComplexApproximation.CauchyRectangle
import Runge.RationalApproximation

/-!
# Cauchy–Pompeiu from rectangular Green's theorem

Subtracting the antiholomorphic part of the real derivative makes the ordinary
difference quotient continuous at its centre. This permits the existing
rectangular Green identity to handle a general smooth function.
-/

open Complex MeasureTheory Set Function Runge
open scoped Topology ContDiff ComplexConjugate

namespace ComplexApproximation

theorem cauchyRiemannDefect_sub {g h : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℝ g z) (hh : DifferentiableAt ℝ h z) :
    cauchyRiemannDefect (fun w => g w - h w) z =
      cauchyRiemannDefect g z - cauchyRiemannDefect h z := by
  simp only [cauchyRiemannDefect, fderiv_fun_sub hg hh,
    sub_apply]
  ring

theorem cauchyRiemannDefect_const_mul_conj (b z : ℂ) :
    cauchyRiemannDefect (fun w : ℂ => b * conj w) z = 2 * I * b := by
  have h := (Complex.conjCLE.hasFDerivAt (x := z)).const_mul b
  change HasFDerivAt (fun w : ℂ => b * conj w)
    (b • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z at h
  rw [cauchyRiemannDefect, h.fderiv]
  change I * (b * conj (1 : ℂ)) - b * conj I = 2 * I * b
  simp only [map_one, conj_I]
  ring

noncomputable def antiholomorphicCoefficient (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  cauchyRiemannDefect g z / (2 * I)

theorem differentiableAt_sub_antiholomorphic {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℝ g z) :
    DifferentiableAt ℂ (fun w => g w - antiholomorphicCoefficient g z * conj w) z := by
  have hh : Differentiable ℝ (fun w : ℂ => antiholomorphicCoefficient g z * conj w) :=
    Complex.differentiable_conj.const_mul _
  apply (differentiableAt_complex_iff_defect_eq_zero (hg.sub (hh z))).mpr
  change cauchyRiemannDefect
    (fun w => g w - antiholomorphicCoefficient g z * conj w) z = 0
  rw [cauchyRiemannDefect_sub hg (hh z), cauchyRiemannDefect_const_mul_conj,
    antiholomorphicCoefficient, mul_div_cancel₀ _ (by simp)]
  exact sub_self _

/-- Continuous densities may be multiplied by the singular kernel on any
compact set; no separation between that set and the origin is needed. -/
theorem integrableOn_div_id {q : ℂ → ℂ} (hq : Continuous q)
    {K : Set ℂ} (hK : IsCompact K) :
    IntegrableOn (fun w : ℂ => q w / w) K := by
  simpa only [cauchyKernel, div_eq_mul_inv] using
    (locallyIntegrable_cauchyKernel.continuous_mul hq).integrableOn_isCompact hK

/-- The ordinary area integral on a centred square. -/
noncomputable def squareIntegral (F : ℂ → ℂ) (R : ℝ) : ℂ :=
  ∫ x : ℝ in -R..R, ∫ y : ℝ in -R..R, F (x + y * I)

theorem squareIntegral_eq_setIntegral {F : ℂ → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hF : IntegrableOn F (Icc (-R) R ×ℂ Icc (-R) R)) :
    squareIntegral F R = ∫ w in Icc (-R) R ×ℂ Icc (-R) R, F w := by
  have hm := volume_preserving_equiv_real_prod.symm measurableEquivRealProd
  have hs : measurableEquivRealProd.symm ⁻¹' (Icc (-R) R ×ℂ Icc (-R) R) =
      Icc (-R) R ×ˢ Icc (-R) R := rfl
  have hi : IntegrableOn (fun p : ℝ × ℝ => F (p.1 + p.2 * I))
      (Icc (-R) R ×ˢ Icc (-R) R) := by
    have h := (hm.integrableOn_comp_preimage
      measurableEquivRealProd.symm.measurableEmbedding).mpr hF
    simpa only [Function.comp_def, hs, measurableEquivRealProd_symm_apply,
      mk_eq_add_mul_I] using h
  have he := hm.setIntegral_preimage_emb measurableEquivRealProd.symm.measurableEmbedding F
      (Icc (-R) R ×ℂ Icc (-R) R)
  simp only [hs, measurableEquivRealProd_symm_apply, mk_eq_add_mul_I] at he
  rw [squareIntegral]
  simp_rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R),
    ← integral_Icc_eq_integral_Ioc]
  rw [← setIntegral_prod (fun p : ℝ × ℝ => F (p.1 + p.2 * I))
    (by simpa only [Measure.volume_eq_prod] using hi)]
  exact he

theorem squareIntegral_eq_zero_of_odd (F : ℂ → ℂ) (hF : ∀ w, F (-w) = -F w)
    (R : ℝ) : squareIntegral F R = 0 := by
  have hi (x : ℝ) : (∫ y : ℝ in -R..R, F (-x + y * I)) =
      -(∫ y : ℝ in -R..R, F (x + y * I)) := by
    have ht := intervalIntegral.integral_comp_neg
      (fun y : ℝ => F (-x + y * I)) (a := -R) (b := R)
    simp only [neg_neg] at ht
    rw [← ht]
    calc
      (∫ y : ℝ in -R..R, F (-x + ↑(-y) * I)) =
          ∫ y : ℝ in -R..R, -F (x + y * I) := by
        apply intervalIntegral.integral_congr
        intro y _
        simpa only [ofReal_neg, neg_add, neg_mul] using hF ((x : ℂ) + y * I)
      _ = _ := intervalIntegral.integral_neg
  have h := intervalIntegral.integral_comp_neg
    (fun x : ℝ => ∫ y : ℝ in -R..R, F (x + y * I)) (a := -R) (b := R)
  simp only [ofReal_neg, hi, neg_neg, intervalIntegral.integral_neg] at h
  change -squareIntegral F R = squareIntegral F R at h
  have h2 : (2 : ℂ) * squareIntegral F R = 0 := by linear_combination -h
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

theorem rectangleBoundary_eq_zero_of_even (F : ℂ → ℂ)
    (hF : ∀ w, F (-w) = F w) (R : ℝ) :
    rectangleBoundary F ⟨-R, -R⟩ ⟨R, R⟩ = 0 := by
  have hb : (∫ x : ℝ in -R..R, F (x + ↑(-R) * I)) =
      ∫ x : ℝ in -R..R, F (x + R * I) := by
    have h := intervalIntegral.integral_comp_neg
      (fun x : ℝ => F (x + ↑(-R) * I)) (a := -R) (b := R)
    simp only [neg_neg] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro x _
    simpa only [ofReal_neg, neg_add, neg_mul] using hF ((x : ℂ) + R * I)
  have hv : (∫ y : ℝ in -R..R, F (↑(-R) + y * I)) =
      ∫ y : ℝ in -R..R, F (R + y * I) := by
    have h := intervalIntegral.integral_comp_neg
      (fun y : ℝ => F (↑(-R) + y * I)) (a := -R) (b := R)
    simp only [neg_neg] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro y _
    simpa only [ofReal_neg, neg_add, neg_mul] using hF ((R : ℂ) + y * I)
  simp only [rectangleBoundary, hb, hv, sub_self, zero_add]

theorem squareIntegral_sub {F G : ℂ → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hF : IntegrableOn F (Icc (-R) R ×ℂ Icc (-R) R))
    (hG : IntegrableOn G (Icc (-R) R ×ℂ Icc (-R) R)) :
    squareIntegral (fun w => F w - G w) R = squareIntegral F R - squareIntegral G R := by
  have hFG : IntegrableOn (fun w => F w - G w) (Icc (-R) R ×ℂ Icc (-R) R) := hF.sub hG
  rw [squareIntegral_eq_setIntegral hR hFG,
    squareIntegral_eq_setIntegral hR hF, squareIntegral_eq_setIntegral hR hG]
  exact integral_sub hF hG

theorem squareIntegral_const_mul (F : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    squareIntegral (fun w => c * F w) R = c * squareIntegral F R := by
  simp only [squareIntegral, intervalIntegral.integral_const_mul]

theorem continuousOn_div_id {g : ℂ → ℂ} (hg : Continuous g) :
    ContinuousOn (fun w : ℂ => g w / w) ({0}ᶜ : Set ℂ) := by
  exact hg.continuousOn.div continuousOn_id (fun _ hw => hw)

theorem rectangleBoundary_sub_of_continuousOn_punctured {F G : ℂ → ℂ}
    (hF : ContinuousOn F ({0}ᶜ : Set ℂ)) (hG : ContinuousOn G ({0}ᶜ : Set ℂ))
    {R : ℝ} (hR : 0 < R) :
    rectangleBoundary (fun w => F w - G w) ⟨-R, -R⟩ ⟨R, R⟩ =
      rectangleBoundary F ⟨-R, -R⟩ ⟨R, R⟩ -
        rectangleBoundary G ⟨-R, -R⟩ ⟨R, R⟩ := by
  have hb (t : ℝ) : (t : ℂ) + ↑(-R) * I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      mul_one, zero_mul, zero_add, add_zero, zero_im] at this
    linarith
  have ht (t : ℝ) : (t : ℂ) + ↑R * I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      mul_one, zero_mul, zero_add, add_zero, zero_im] at this
    linarith
  have hl (t : ℝ) : (↑(-R) : ℂ) + ↑t * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero, zero_re] at this
    linarith
  have hr (t : ℝ) : (R : ℂ) + ↑t * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero, zero_re] at this
    linarith
  have ci (H : ℂ → ℂ) (hH : ContinuousOn H ({0}ᶜ : Set ℂ))
      (γ : ℝ → ℂ) (hγ : Continuous γ) (hγ0 : ∀ t, γ t ≠ 0) :
      IntervalIntegrable (fun t => H (γ t)) volume (-R) R :=
    (hH.comp_continuous hγ hγ0).intervalIntegrable _ _
  simp only [rectangleBoundary]
  rw [intervalIntegral.integral_sub (ci F hF _ (by fun_prop) hb)
      (ci G hG _ (by fun_prop) hb),
    intervalIntegral.integral_sub (ci F hF _ (by fun_prop) ht)
      (ci G hG _ (by fun_prop) ht),
    intervalIntegral.integral_sub (ci F hF _ (by fun_prop) hr)
      (ci G hG _ (by fun_prop) hr),
    intervalIntegral.integral_sub (ci F hF _ (by fun_prop) hl)
      (ci G hG _ (by fun_prop) hl)]
  ring

theorem rectangleBoundary_congr_on_punctured {F G : ℂ → ℂ}
    (hFG : EqOn F G ({0}ᶜ : Set ℂ)) {R : ℝ} (hR : 0 < R) :
    rectangleBoundary F ⟨-R, -R⟩ ⟨R, R⟩ =
      rectangleBoundary G ⟨-R, -R⟩ ⟨R, R⟩ := by
  have hK : ({0} : Set ℂ) ⊆ Ioo (-R) R ×ℂ Ioo (-R) R := by
    simp only [singleton_subset_iff, mem_reProdIm, mem_Ioo, zero_re, zero_im]
    exact ⟨⟨by linarith, hR⟩, ⟨by linarith, hR⟩⟩
  have hb (t : ℝ) := hFG (bottom_line_avoids (a := ⟨-R, -R⟩) (b := ⟨R, R⟩) hK t)
  have ht (t : ℝ) := hFG (top_line_avoids (a := ⟨-R, -R⟩) (b := ⟨R, R⟩) hK t)
  have hr (t : ℝ) := hFG (right_line_avoids (a := ⟨-R, -R⟩) (b := ⟨R, R⟩) hK t)
  have hl (t : ℝ) := hFG (left_line_avoids (a := ⟨-R, -R⟩) (b := ⟨R, R⟩) hK t)
  simp only [rectangleBoundary, hb, ht, hr, hl]

/-- The centred rectangular Cauchy–Pompeiu identity, before evaluating the
boundary integral of the Cauchy kernel. -/
theorem cauchyPompeiu_square (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g)
    {R : ℝ} (hR : 0 < R) :
    rectangleBoundary (fun w => g w / w) ⟨-R, -R⟩ ⟨R, R⟩ -
        g 0 * rectangleBoundary (fun w : ℂ => w⁻¹) ⟨-R, -R⟩ ⟨R, R⟩ =
      squareIntegral (fun w => cauchyRiemannDefect g w / w) R := by
  let b := antiholomorphicCoefficient g 0
  let h : ℂ → ℂ := fun w => g w - b * conj w
  have hconj : ContDiff ℝ ∞ (fun w : ℂ => conj w) := Complex.conjCLE.contDiff
  have hh : ContDiff ℝ ∞ h := hg.sub (contDiff_const.mul hconj)
  have hd (w : ℂ) : cauchyRiemannDefect h w = cauchyRiemannDefect g w - 2 * I * b := by
    exact (cauchyRiemannDefect_sub (hg.differentiable (by simp) w)
      ((Complex.differentiable_conj.const_mul b) w)).trans
        (congrArg (fun c => cauchyRiemannDefect g w - c)
          (cauchyRiemannDefect_const_mul_conj b w))
  have hs : IsCompact (Icc (-R) R ×ℂ Icc (-R) R) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hih := integrableOn_div_id (continuous_cauchyRiemannDefect hh) hs
  have hig := integrableOn_div_id (continuous_cauchyRiemannDefect hg) hs
  have hik := integrableOn_div_id (q := fun _ : ℂ => 2 * I * b) continuous_const hs
  have harea : squareIntegral (fun w => cauchyRiemannDefect h w / w) R =
      squareIntegral (fun w => cauchyRiemannDefect g w / w) R := by
    simp_rw [hd, sub_div]
    rw [squareIntegral_sub hR.le hig hik]
    have hz := squareIntegral_eq_zero_of_odd (fun w : ℂ => w⁻¹) (by simp) R
    simp only [div_eq_mul_inv, squareIntegral_const_mul, hz, mul_zero, sub_zero]
  have H := rectangleBoundary_dslope h hh.continuous (hh.differentiable (by simp))
    0 ⟨-R, -R⟩ ⟨R, R⟩ (differentiableAt_sub_antiholomorphic
      (hg.differentiable (by simp) 0))
    (by simpa only [sub_zero, uIcc_of_le (by linarith : -R ≤ R)] using hih)
  change rectangleBoundary (dslope h 0) ⟨-R, -R⟩ ⟨R, R⟩ =
    squareIntegral (fun w => cauchyRiemannDefect h w / (w - 0)) R at H
  simp only [sub_zero] at H
  rw [harea] at H
  have heq : EqOn (dslope h 0)
      (fun w => (g w / w - b * conj w / w) - g 0 * w⁻¹) ({0}ᶜ : Set ℂ) := by
    intro w hw
    rw [dslope_of_ne _ hw, slope_def_field]
    simp only [h, map_zero, mul_zero, sub_zero, div_eq_mul_inv]
    ring
  rw [rectangleBoundary_congr_on_punctured heq hR] at H
  have hcg := continuousOn_div_id hg.continuous
  have hcb : ContinuousOn (fun w : ℂ => b * conj w / w) ({0}ᶜ : Set ℂ) :=
    continuousOn_div_id (continuous_const.mul hconj.continuous)
  have hcz := continuousOn_div_id (continuous_const (y := g 0))
  have hbzero : rectangleBoundary (fun w : ℂ => b * conj w / w)
      ⟨-R, -R⟩ ⟨R, R⟩ = 0 := by
    apply rectangleBoundary_eq_zero_of_even
    intro w
    simp
  have hs1 := rectangleBoundary_sub_of_continuousOn_punctured hcg hcb hR
  have hcgb : ContinuousOn (fun w => g w / w - b * conj w / w) ({0}ᶜ : Set ℂ) :=
    hcg.sub hcb
  have hcz' : ContinuousOn (fun w : ℂ => g 0 * w⁻¹) ({0}ᶜ : Set ℂ) :=
    by simpa only [div_eq_mul_inv] using hcz
  have hs2 := rectangleBoundary_sub_of_continuousOn_punctured hcgb hcz' hR
  rw [hs2, hs1, hbzero, sub_zero, rectangleBoundary_const_mul] at H
  exact H

theorem rectangleBoundary_eq_zero_of_support {F : ℂ → ℂ} {a b : ℂ}
    (hF : support F ⊆ Ioo a.re b.re ×ℂ Ioo a.im b.im) :
    rectangleBoundary F a b = 0 := by
  have hb (t : ℝ) : F (t + a.im * I) = 0 := by
    simpa only [Function.mem_support, not_not] using bottom_line_avoids hF t
  have ht (t : ℝ) : F (t + b.im * I) = 0 := by
    simpa only [Function.mem_support, not_not] using top_line_avoids hF t
  have hr (t : ℝ) : F (b.re + t * I) = 0 := by
    simpa only [Function.mem_support, not_not] using right_line_avoids hF t
  have hl (t : ℝ) : F (a.re + t * I) = 0 := by
    simpa only [Function.mem_support, not_not] using left_line_avoids hF t
  simp only [rectangleBoundary, hb, ht, hr, hl, intervalIntegral.integral_zero,
    mul_zero, sub_zero, add_zero]

theorem integrable_defect_div_id {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) :
    Integrable (fun w : ℂ => cauchyRiemannDefect g w / w) := by
  simpa only [cauchyKernel, div_eq_mul_inv, smul_eq_mul] using
    locallyIntegrable_cauchyKernel.integrable_smul_left_of_hasCompactSupport
      (continuous_cauchyRiemannDefect hg) (hasCompactSupport_cauchyRiemannDefect hc)

/-- Cauchy–Pompeiu for a smooth compactly supported function, at the origin.
The Cauchy–Riemann defect used by the Runge library is `2i` times `∂̄`. -/
theorem integral_defect_div_id (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) :
    (∫ w : ℂ, cauchyRiemannDefect g w / w) = -(2 * Real.pi * I) * g 0 := by
  obtain ⟨R, hR, hbound⟩ :=
    (hc.union (hasCompactSupport_cauchyRiemannDefect hc)).isBounded.exists_pos_norm_lt
  have hrect {z : ℂ} (hz : z ∈ tsupport g ∪ tsupport (cauchyRiemannDefect g)) :
      z ∈ Ioo (-R) R ×ℂ Ioo (-R) R :=
    ⟨abs_lt.mp ((abs_re_le_norm z).trans_lt (hbound z hz)),
      abs_lt.mp ((abs_im_le_norm z).trans_lt (hbound z hz))⟩
  have hboundary : rectangleBoundary (fun w : ℂ => g w / w) ⟨-R, -R⟩ ⟨R, R⟩ = 0 := by
    apply rectangleBoundary_eq_zero_of_support
    intro z hz
    apply hrect (Or.inl (subset_tsupport g ?_))
    intro hzero
    exact hz (by simp [hzero])
  have H := cauchyPompeiu_square g hg hR
  rw [hboundary, rectangleBoundary_inv R hR, zero_sub] at H
  have hi := integrable_defect_div_id hg hc
  rw [squareIntegral_eq_setIntegral hR.le hi.integrableOn,
    setIntegral_eq_integral_of_forall_compl_eq_zero] at H
  · rw [← H]
    ring
  · intro z hz
    by_contra hne
    have hdz : cauchyRiemannDefect g z ≠ 0 := by
      intro hzero
      exact hne (by simp [hzero])
    have hm := hrect (Or.inr (subset_tsupport _ hdz))
    exact hz ⟨⟨hm.1.1.le, hm.1.2.le⟩, ⟨hm.2.1.le, hm.2.2.le⟩⟩

theorem cauchyRiemannDefect_comp_sub_left {g : ℂ → ℂ} (hg : Differentiable ℝ g)
    (z w : ℂ) :
    cauchyRiemannDefect (fun u => g (z - u)) w = -cauchyRiemannDefect g (z - w) := by
  have hd := (hg (z - w)).hasFDerivAt.comp w ((hasFDerivAt_id w).const_sub z)
  change HasFDerivAt (fun u => g (z - u)) _ w at hd
  rw [cauchyRiemannDefect, hd.fderiv, cauchyRiemannDefect]
  simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply, map_neg]
  ring

/-- The unnormalised Cauchy transform reproduces a smooth compactly supported
function from its Cauchy–Riemann defect. -/
theorem cauchyTransform_defect (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (z : ℂ) :
    cauchyTransform (cauchyRiemannDefect g) z = (2 * Real.pi * I) * g z := by
  have hgs : ContDiff ℝ ∞ (fun w => g (z - w)) := hg.comp (contDiff_const.sub contDiff_id)
  have hcs : HasCompactSupport (fun w => g (z - w)) := by
    exact hc.comp_homeomorph ((Homeomorph.neg ℂ).trans (Homeomorph.addLeft z))
  have H := integral_defect_div_id (fun w => g (z - w)) hgs hcs
  simp only [cauchyRiemannDefect_comp_sub_left (hg.differentiable (by simp)),
    sub_zero, div_eq_inv_mul, mul_neg, integral_neg] at H
  change -cauchyTransform (cauchyRiemannDefect g) z = -(2 * Real.pi * I) * g z at H
  linear_combination -H

/-- The Cauchy transform is a right inverse after multiplication by `1/(2πi)`.
This statement also holds at points inside the support of the density. -/
theorem cauchyRiemannDefect_cauchyTransform_eq (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (z : ℂ) :
    cauchyRiemannDefect (cauchyTransform g) z = (2 * Real.pi * I) * g z := by
  rw [cauchyRiemannDefect_cauchyTransform hg hc, cauchyTransform_defect g hg hc]

/-- A smooth solution of the inhomogeneous Cauchy–Riemann defect equation. -/
noncomputable def solveCauchyRiemann (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ * cauchyTransform g z

theorem contDiff_solveCauchyRiemann {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) : ContDiff ℝ ∞ (solveCauchyRiemann g) :=
  contDiff_const.mul (contDiff_cauchyTransform hg hc)

theorem cauchyRiemannDefect_solveCauchyRiemann (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (z : ℂ) :
    cauchyRiemannDefect (solveCauchyRiemann g) z = g z := by
  have hd := (contDiff_cauchyTransform hg hc).differentiable (by simp) z
  change cauchyRiemannDefect (fun w => (2 * Real.pi * I : ℂ)⁻¹ * cauchyTransform g w) z = g z
  rw [cauchyRiemannDefect_mul hd (differentiableAt_const _),
    cauchyRiemannDefect_cauchyTransform_eq g hg hc]
  have hn : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  exact inv_mul_cancel_left₀ hn _

theorem cauchyPompeiu_compact (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) : solveCauchyRiemann (cauchyRiemannDefect g) = g := by
  funext z
  rw [solveCauchyRiemann, cauchyTransform_defect g hg hc]
  have hn : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  exact inv_mul_cancel_left₀ hn _

end ComplexApproximation
