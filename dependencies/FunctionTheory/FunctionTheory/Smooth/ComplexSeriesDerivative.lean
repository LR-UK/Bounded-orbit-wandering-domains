import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Normed.Operator.Bilinear

open Set Function Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Complex differentiability at a point is preserved by a series controlled
in the real derivative norm. The summands need only be complex differentiable
at this point; their holomorphic neighbourhoods need not be uniform.
This is the boundary Cauchy--Riemann step in smooth conjugacy limits. -/
theorem hasFDerivAt_complex_tsum_of_real_control
    (u : ℕ → ℂ → ℂ) (hu : ∀ i, Differentiable ℝ (u i))
    (b : ℕ → ℝ) (hb : Summable b)
    (hbound : ∀ i z, ‖fderiv ℝ (u i) z‖ ≤ b i)
    {x₀ : ℂ} (hsum₀ : Summable (fun i => u i x₀))
    {a : ℂ} (hcomplex : ∀ i, DifferentiableAt ℂ (u i) a) :
    HasFDerivAt (fun z => ∑' i, u i z) (∑' i, fderiv ℂ (u i) a) a := by
  have Hreal := hasFDerivAt_tsum hb (fun i z => (hu i z).hasFDerivAt)
    hbound hsum₀ a
  have Hnorm : ∀ i, ‖fderiv ℂ (u i) a‖ ≤ b i := by
    intro i
    have H := hbound i a
    rw [(hcomplex i).fderiv_restrictScalars ℝ,
      ContinuousLinearMap.norm_restrictScalars] at H
    exact H
  have Hsum : Summable (fun i => fderiv ℂ (u i) a) :=
    Summable.of_norm_bounded hb Hnorm
  let R := ContinuousLinearMap.restrictScalarsL ℂ ℂ ℂ ℝ ℝ
  have HR : (∑' i, fderiv ℂ (u i) a).restrictScalars ℝ =
      ∑' i, fderiv ℝ (u i) a := by
    calc
      _ = ∑' i, (fderiv ℂ (u i) a).restrictScalars ℝ := R.map_tsum Hsum
      _ = _ := tsum_congr (fun i => ((hcomplex i).fderiv_restrictScalars ℝ).symm)
  exact hasFDerivAt_of_restrictScalars ℝ Hreal HR

end FunctionTheory
