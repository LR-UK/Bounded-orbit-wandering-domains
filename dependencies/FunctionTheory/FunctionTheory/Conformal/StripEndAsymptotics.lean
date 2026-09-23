import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Local estimates at the reflected end of a strip

These are the analytic estimates after a conformal map has been reflected
across the boundary near zero. The geometric reflection and end-identification
steps remain separate hypotheses in an application to a strip.
-/

open Filter Asymptotics
open scoped Topology

namespace FunctionTheory

theorem analyticAt_dslope {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    AnalyticAt ℂ (dslope f a) a := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨_, hp.has_fpower_series_dslope_fslope⟩

/-- At a simple zero, the logarithmic derivative multiplied by the coordinate
is `1 + O(z)`. This is the derivative estimate in the strip-end argument. -/
theorem isBigO_mul_logDeriv_sub_one_at_simple_zero {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) (hd : deriv f 0 ≠ 0) :
    (fun z => z * deriv f z / f z - 1) =O[𝓝[≠] 0] (fun z => z) := by
  let q := dslope f 0
  have hq : AnalyticAt ℂ q 0 := analyticAt_dslope hf
  have hq0 : q 0 = deriv f 0 := dslope_same f 0
  have hH : DifferentiableAt ℂ (fun z => deriv f z / q z) 0 :=
    (hf.deriv.div hq (hq0 ▸ hd)).differentiableAt
  have hO : (fun z => deriv f z / q z - 1) =O[𝓝 0] (fun z => z) := by
    simpa only [hq0, div_self hd, sub_zero] using hH.isBigO_sub
  apply (hO.mono nhdsWithin_le_nhds).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzne : z ≠ 0 := hz
  have hfactor : f z = z * q z := by
    simpa only [sub_zero, hf0, smul_eq_mul] using (sub_smul_dslope f 0 z).symm
  rw [hfactor]
  congr 1
  exact (mul_div_mul_left (deriv f z) (q z) hzne).symm

/-- The logarithm of the regularized quotient has a linear error at a simple
zero, with the usual slit-plane condition on the leading coefficient. -/
theorem isBigO_log_quotient_sub_log_deriv {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (hd : deriv f 0 ∈ Complex.slitPlane) :
    (fun z => Complex.log (f z / z) - Complex.log (deriv f 0))
      =O[𝓝[≠] 0] (fun z => z) := by
  let q := dslope f 0
  have hq : AnalyticAt ℂ q 0 := analyticAt_dslope hf
  have hq0 : q 0 = deriv f 0 := dslope_same f 0
  have hH := (hq.clog (hq0 ▸ hd)).differentiableAt.isBigO_sub
  have hO : (fun z => Complex.log (q z) - Complex.log (deriv f 0))
      =O[𝓝 0] (fun z => z) := by
    simpa only [hq0, sub_zero] using hH
  apply (hO.mono nhdsWithin_le_nhds).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzne : z ≠ 0 := hz
  have hfactor : f z = z * q z := by
    simpa only [sub_zero, hf0, smul_eq_mul] using (sub_smul_dslope f 0 z).symm
  rw [hfactor, mul_div_cancel_left₀ _ hzne]

/-- The exponential coordinate tends to the punctured origin uniformly as
the real part tends to positive infinity. No restriction on imaginary parts
is needed for this coordinate estimate. -/
theorem tendsto_exp_neg_re_atTop :
    Tendsto (fun z : ℂ => Complex.exp (-z)) (comap Complex.re atTop) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Function.comp_def, Complex.norm_exp, Complex.neg_re] using
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (show Tendsto Complex.re (comap Complex.re atTop) atTop from tendsto_comap))
  · exact .of_forall fun z => Complex.exp_ne_zero (-z)

theorem isBigO_comp_exp_neg {g : ℂ → ℂ}
    (h : g =O[𝓝[≠] 0] (fun z => z)) :
    (fun z => g (Complex.exp (-z))) =O[comap Complex.re atTop]
      (fun z => Real.exp (-z.re)) := by
  simpa only [Function.comp_def, Complex.norm_exp, Complex.neg_re] using
    (h.comp_tendsto tendsto_exp_neg_re_atTop).norm_right

/-- The quantitative derivative estimate after the reflected map at zero has
been supplied. This does not assert the geometric reflection hypotheses. -/
theorem stripEnd_logDeriv_estimate {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) (hd : deriv f 0 ≠ 0) :
    (fun z => Complex.exp (-z) * deriv f (Complex.exp (-z)) /
      f (Complex.exp (-z)) - 1) =O[comap Complex.re atTop]
        (fun z => Real.exp (-z.re)) :=
  isBigO_comp_exp_neg (isBigO_mul_logDeriv_sub_one_at_simple_zero hf hf0 hd)

/-- The corresponding logarithmic quotient estimate in the exponential
coordinate; identifying the strip map's logarithm branch is a separate step. -/
theorem stripEnd_log_quotient_estimate {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (hd : deriv f 0 ∈ Complex.slitPlane) :
    (fun z => Complex.log (f (Complex.exp (-z)) / Complex.exp (-z)) -
      Complex.log (deriv f 0)) =O[comap Complex.re atTop]
        (fun z => Real.exp (-z.re)) :=
  isBigO_comp_exp_neg (isBigO_log_quotient_sub_log_deriv hf hf0 hd)

end FunctionTheory
