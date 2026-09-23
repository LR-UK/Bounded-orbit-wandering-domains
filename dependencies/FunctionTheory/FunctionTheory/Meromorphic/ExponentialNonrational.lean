import FunctionTheory.Meromorphic.RationalInfinity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.CauchyIntegral

open Set Filter Bornology
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- The exponential is nonrational as a meromorphic function, not only
nonpolynomial as an entire function. -/
theorem not_rational_meromorphic_exp : ¬ IsRationalMeromorphic Complex.exp := by
  have hnf : MeromorphicNFOn Complex.exp univ := fun z _ =>
    (Complex.differentiable_exp.analyticAt z).meromorphicNFAt
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have ha : Tendsto (fun n : ℕ => (n : ℂ)) atTop (cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    simpa only [Complex.norm_natCast] using hnat
  have hb : Tendsto (fun n : ℕ => (n : ℂ) * Complex.I) atTop (cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    simpa only [norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast] using hnat
  have hfa : Tendsto (fun n : ℕ => Complex.exp n) atTop (cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    simpa only [Complex.norm_exp, Complex.natCast_re, Function.comp_def] using Real.tendsto_exp_atTop.comp hnat
  apply not_rational_meromorphic_of_two_sequences hnf
    (fun n : ℕ => (n : ℂ)) (fun n : ℕ => (n : ℂ) * Complex.I) ha hb hfa 1
  intro n
  simp [Complex.norm_exp, Complex.mul_re]

end FunctionTheory
