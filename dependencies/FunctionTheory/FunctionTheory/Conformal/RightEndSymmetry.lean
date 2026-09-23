import FunctionTheory.Conformal.RightEndNormalization
import Mathlib.Analysis.Calculus.Deriv.Star

open Set Metric Complex Function Filter
open scoped Topology ComplexConjugate

namespace FunctionTheory

/-- End-normalized disk maps inherit reflection symmetry of their domain. -/
theorem IsRightEndRiemannMapOn.conj_eq
    {U : Set ℂ} {f : ℂ → ℂ} {x₀ R : ℝ}
    (hf : IsRightEndRiemannMapOn f U (x₀ : ℂ))
    (hUo : IsOpen U) (hUS : U ⊆ standardHorizontalStrip)
    (htail : ∀ z ∈ standardHorizontalStrip, R < z.re → z ∈ U)
    (hconj : MapsTo conj U U) :
    ∀ z ∈ U, f (conj z) = conj (f z) := by
  let g : ℂ → ℂ := conj ∘ f ∘ conj
  have hcb : BijOn conj U U :=
    ⟨hconj, Complex.conjCLE.injective.injOn, fun z hz => ⟨conj z, hconj hz, by simp⟩⟩
  have hcD : BijOn conj (ball (0 : ℂ) 1) (ball 0 1) := by
    refine ⟨?_, Complex.conjCLE.injective.injOn, ?_⟩
    · intro z hz; simpa using hz
    · intro z hz; exact ⟨conj z, by simpa using hz, by simp⟩
  have hgd : DifferentiableOn ℂ g U := by
    intro z hz
    have hd := ((hf.differentiableOn (conj z) (hconj hz)).differentiableAt
      (hUo.mem_nhds (hconj hz))).conj_conj
    simpa [g] using hd.differentiableWithinAt (s := U)
  have hΩconj : MapsTo conj (exponentialImage U) (exponentialImage U) := by
    rintro w ⟨z, hz, rfl⟩
    refine ⟨conj z, hconj hz, ?_⟩
    simp only [← exp_conj, map_neg]
  have hc : Tendsto conj (𝓝[exponentialImage U] (0 : ℂ)) (𝓝[exponentialImage U] 0) := by
    simpa using (continuous_conj.continuousWithinAt (x := (0 : ℂ))).tendsto_nhdsWithin hΩconj
  have hlim := continuous_conj.continuousAt.tendsto.comp (hf.end_limit.comp hc)
  have he : (fun w => conj (f (-log (conj w)))) =ᶠ[𝓝[exponentialImage U] 0]
      (fun w => g (-log w)) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hp : 0 < w.re := by
      obtain ⟨z, hz, rfl⟩ := hw
      exact re_exp_neg_pos_of_mem_strip (hUS hz)
    have ha : w.arg ≠ Real.pi := by
      have h := (abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hp))).2
      linarith [Real.pi_pos]
    simp only [g, Function.comp_apply, log_conj w ha, map_neg]
  have hg : IsRightEndRiemannMapOn g U (x₀ : ℂ) := by
    refine ⟨hf.base_mem, hgd, hcD.comp (hf.bijOn.comp hcb), ?_, ?_⟩
    · simp only [g, Function.comp_apply, conj_ofReal, hf.map_base, map_zero]
    · simpa only [map_one] using hlim.congr' he
  have heq := hg.eqOn hf hUo hUS htail
  intro z hz
  have h := congrArg conj (heq hz)
  simpa [g] using h

/-- The exponential endpoint limit implies the ordinary limit along the
positive real direction. -/
theorem IsRightEndRiemannMapOn.tendsto_real_atTop
    {U : Set ℂ} {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hf : IsRightEndRiemannMapOn f U z₀)
    (htail : ∀ z ∈ standardHorizontalStrip, R < z.re → z ∈ U) :
    Tendsto (fun t : ℝ => f (t : ℂ)) atTop (𝓝 1) := by
  have hc : Tendsto (fun t : ℝ => exp (-(t : ℂ))) atTop (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def, ofReal_zero, ofReal_exp, ofReal_neg] using
      continuous_ofReal.continuousAt.tendsto.comp
        (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)
  have hΩ : ∀ᶠ t : ℝ in atTop, exp (-(t : ℂ)) ∈ exponentialImage U := by
    filter_upwards [eventually_gt_atTop R] with t ht
    exact ⟨(t : ℂ), htail _ (by simpa [standardHorizontalStrip] using half_pos Real.pi_pos) ht, rfl⟩
  have h := hf.end_limit.comp (tendsto_nhdsWithin_iff.mpr ⟨hc, hΩ⟩)
  convert h using 1
  ext t
  rw [Function.comp_apply, neg_log_exp_neg_of_mem_strip
    (by simpa [standardHorizontalStrip] using half_pos Real.pi_pos)]

end FunctionTheory
