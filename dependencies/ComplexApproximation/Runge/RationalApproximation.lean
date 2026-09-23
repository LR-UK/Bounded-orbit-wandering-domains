import Runge.IntegralTransforms
import Runge.RectangleKernel

open Complex Polynomial MeasureTheory Set Function
open scoped Topology ContDiff

namespace Runge

theorem rectangleBoundary_const_mul (F : ℂ → ℂ) (c a b : ℂ) :
    rectangleBoundary (fun w => c * F w) a b = c * rectangleBoundary F a b := by
  simp only [rectangleBoundary, intervalIntegral.integral_const_mul]
  ring

theorem dslope_eq_of_value_zero (g : ℂ → ℂ) (z w : ℂ) (hw : w ≠ z) (hg : g w = 0) :
    dslope g z w = -g z * (w-z)⁻¹ := by
  rw [dslope_of_ne g hw, slope_def_field, hg]
  simp [div_eq_mul_inv]

theorem rectangleBoundary_dslope_of_support (g : ℂ → ℂ) (a b z : ℂ)
    (hs : tsupport g ⊆ Ioo a.re b.re ×ℂ Ioo a.im b.im)
    (hz : z ∈ Ioo a.re b.re ×ℂ Ioo a.im b.im) :
    rectangleBoundary (dslope g z) a b =
      -g z * rectangleBoundary (fun w => (w-z)⁻¹) a b := by
  rw [← rectangleBoundary_const_mul]
  have hb (t : ℝ) : dslope g z (t + a.im * I) =
      -g z * (t + a.im * I-z)⁻¹ := by
    apply dslope_eq_of_value_zero
    · intro h
      have he := congrArg Complex.im h
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one,
        zero_mul, add_zero, zero_add] at he
      exact (ne_of_lt hz.2.1) he
    · exact image_eq_zero_of_notMem_tsupport (bottom_line_avoids hs t)
  have ht (t : ℝ) : dslope g z (t + b.im * I) =
      -g z * (t + b.im * I-z)⁻¹ := by
    apply dslope_eq_of_value_zero
    · intro h
      have he := congrArg Complex.im h
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one,
        zero_mul, add_zero, zero_add] at he
      exact (ne_of_gt hz.2.2) he
    · exact image_eq_zero_of_notMem_tsupport (top_line_avoids hs t)
  have hr (t : ℝ) : dslope g z (b.re + t * I) =
      -g z * (b.re + t * I-z)⁻¹ := by
    apply dslope_eq_of_value_zero
    · intro h
      have he := congrArg Complex.re h
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
        zero_mul, sub_zero, add_zero] at he
      exact (ne_of_gt hz.1.2) he
    · exact image_eq_zero_of_notMem_tsupport (right_line_avoids hs t)
  have hl (t : ℝ) : dslope g z (a.re + t * I) =
      -g z * (a.re + t * I-z)⁻¹ := by
    apply dslope_eq_of_value_zero
    · intro h
      have he := congrArg Complex.re h
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
        zero_mul, sub_zero, add_zero] at he
      exact (ne_of_lt hz.1.1) he
    · exact image_eq_zero_of_notMem_tsupport (left_line_avoids hs t)
  simp only [rectangleBoundary, hb, ht, hr, hl]

theorem exists_rectangle_containing_compact (S : Set ℂ) (hS : IsCompact S) :
    ∃ a b : ℂ, S ⊆ Ioo a.re b.re ×ℂ Ioo a.im b.im := by
  obtain ⟨R, _, hR⟩ := hS.isBounded.exists_pos_norm_lt
  refine ⟨⟨-R, -R⟩, ⟨R, R⟩, ?_⟩
  intro z hz
  exact ⟨abs_lt.mp ((abs_re_le_norm z).trans_lt (hR z hz)),
    abs_lt.mp ((abs_im_le_norm z).trans_lt (hR z hz))⟩

set_option maxHeartbeats 800000 in
theorem smooth_extension_mem_rationalClosure (K : Set ℂ) [CompactSpace K]
    (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hd : ∀ z ∈ K, DifferentiableAt ℂ g z)
    (hsep : Disjoint (tsupport (cauchyRiemannDefect g)) K) :
    (⟨fun z : K => g z, hg.continuous.comp continuous_subtype_val⟩ : C(K, ℂ))
      ∈ rationalClosure K := by
  have hK : IsCompact K := isCompact_iff_compactSpace.mpr inferInstance
  obtain ⟨a, b, hab⟩ := exists_rectangle_containing_compact (K ∪ tsupport g) (hK.union hgc)
  have hKR : K ⊆ Ioo a.re b.re ×ℂ Ioo a.im b.im := fun _ hz => hab (Or.inl hz)
  have hgR : tsupport g ⊆ Ioo a.re b.re ×ℂ Ioo a.im b.im := fun _ hz => hab (Or.inr hz)
  let G : C(K, ℂ) := ⟨fun z => g z, hg.continuous.comp continuous_subtype_val⟩
  let B := boundaryCauchyTransform K a b hKR
  let A := areaCauchyTransform K (cauchyRiemannDefect g)
    (continuous_cauchyRiemannDefect hg) hsep a b
  have hA : A ∈ rationalClosure K := areaCauchyTransform_mem K _ _ _ a b
  have hB : B ∈ rationalClosure K := boundaryCauchyTransform_mem K a b hKR
  have hu : IsUnit B := B.isUnit_iff_forall_ne_zero.mpr fun z => by
    rw [boundaryCauchyTransform_apply]
    exact rectangleKernel_ne_zero a b z (hKR z.property).1.1 (hKR z.property).1.2
      (hKR z.property).2.1 (hKR z.property).2.2
  have hGB : G * B = -A := by
    apply ContinuousMap.ext
    intro z
    have hk : Continuous (fun w : ℂ => cauchyRiemannDefect g w / (w-(z : ℂ))) :=
      (continuous_cauchyKernel K (cauchyRiemannDefect g)
        (continuous_cauchyRiemannDefect hg) hsep).comp
        (show Continuous (fun w : ℂ => (w, z)) from continuous_id.prodMk continuous_const)
    have hi : IntegrableOn (fun w : ℂ => cauchyRiemannDefect g w / (w-(z : ℂ)))
        (Set.uIcc a.re b.re ×ℂ Set.uIcc a.im b.im) :=
      hk.continuousOn.integrableOn_compact (isCompact_uIcc.reProdIm isCompact_uIcc)
    have he := rectangleBoundary_dslope g hg.continuous (hg.differentiable (by simp)) z a b
      (hd z z.property) hi
    rw [rectangleBoundary_dslope_of_support g a b z hgR (hKR z.property)] at he
    change g z * boundaryCauchyTransform K a b hKR z = -areaCauchyTransform K _ _ _ a b z
    rw [boundaryCauchyTransform_apply, areaCauchyTransform_apply, ← he]
    ring
  have heq : G = (-A) * Ring.inverse B := by
    calc
      G = (G * B) * Ring.inverse B := (Ring.mul_inverse_cancel_right B G hu).symm
      _ = (-A) * Ring.inverse B := by rw [hGB]
  rw [show (⟨fun z : K => g z, hg.continuous.comp continuous_subtype_val⟩ : C(K, ℂ)) = G from rfl, heq]
  exact (rationalClosure K).mul_mem ((rationalClosure K).neg_mem hA)
    (ringInverse_mem_rationalClosure K B hB hu)

/-- Runge's rational approximation theorem for an arbitrary compact subset of
the complex plane and a function analytic on an open neighbourhood. -/
theorem rational_approximation (K : Set ℂ) (hK : IsCompact K)
    (U : Set ℂ) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : ℂ[X], (∀ z ∈ K, q.eval z ≠ 0) ∧
      (∀ z ∈ K, ‖f z - p.eval z / q.eval z‖ < ε) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨g, hg, hgc, hgf, hsep⟩ := exists_extension_with_separated_defect K U hK hU hKU f hf
  have hd (z : ℂ) (hz : z ∈ K) : DifferentiableAt ℂ g z :=
    (hf z (hKU hz)).differentiableAt.congr_of_eventuallyEq (hgf z hz)
  obtain ⟨p, q, hq, hpq⟩ := (mem_rationalClosure_iff K _).mp
    (smooth_extension_mem_rationalClosure K g hg hgc hd hsep) ε hε
  refine ⟨p, q, fun z hz => hq ⟨z, hz⟩, fun z hz => ?_⟩
  have he := (hgf z hz).self_of_nhds
  simpa only [ContinuousMap.coe_mk, he] using hpq ⟨z, hz⟩

end Runge
