import FunctionTheory.Meromorphic.Sphere
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

open Set Filter Polynomial Bornology
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Rationality is a statement about meromorphic germs, so it does not depend
on arbitrary representative values at poles or removable singularities. -/
def IsRationalMeromorphic (f : ℂ → ℂ) : Prop :=
  ∃ p q : ℂ[X], q ≠ 0 ∧
    ∀ a : ℂ, f =ᶠ[𝓝[≠] a] (fun z => p.eval z / q.eval z)

private theorem polynomial_at_inverse_meromorphic (p : ℂ[X]) :
    MeromorphicAt (fun z : ℂ => p.eval z⁻¹) 0 := by
  have hi : MeromorphicAt (fun z : ℂ => z⁻¹) 0 := by fun_prop
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Polynomial.eval_add] using hp.fun_add hq
  | monomial n a =>
    simpa only [Polynomial.eval_monomial] using
      (analyticAt_const.meromorphicAt.fun_mul (hi.fun_pow n) :
        MeromorphicAt (fun z : ℂ => a * (z⁻¹) ^ n) 0)

/-- A rational function has one finite limit or tends to infinity as its
argument tends to infinity in the plane. -/
theorem rational_limit_at_infinity (p q : ℂ[X]) :
    (∃ c : ℂ, Tendsto (fun z => p.eval z / q.eval z) (cobounded ℂ) (𝓝 c)) ∨
      Tendsto (fun z => p.eval z / q.eval z) (cobounded ℂ) (cobounded ℂ) := by
  let R : ℂ → ℂ := fun z => p.eval z⁻¹ / q.eval z⁻¹
  have hR : MeromorphicAt R 0 :=
    (polynomial_at_inverse_meromorphic p).div (polynomial_at_inverse_meromorphic q)
  by_cases ho : meromorphicOrderAt R 0 < 0
  · right
    simpa only [R, Function.comp_def, inv_inv] using
      (tendsto_cobounded_of_meromorphicOrderAt_neg ho).comp tendsto_inv₀_cobounded'
  · obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hR (le_of_not_gt ho)
    left
    refine ⟨c, ?_⟩
    simpa only [R, Function.comp_def, inv_inv] using hc.comp tendsto_inv₀_cobounded'

/-- A normal representative with rational germs has the same dichotomy. -/
theorem rational_meromorphic_limit_at_infinity
    {f : ℂ → ℂ} (hf : MeromorphicNFOn f univ) (hr : IsRationalMeromorphic f) :
    (∃ c : ℂ, Tendsto f (cobounded ℂ) (𝓝 c)) ∨
      Tendsto f (cobounded ℂ) (cobounded ℂ) := by
  obtain ⟨p, q, hq, heq⟩ := hr
  have hqevent : ∀ᶠ z : ℂ in cobounded ℂ, q.eval z ≠ 0 := by
    have H := (Polynomial.eventually_eval_ne_zero_cofinite hq).filter_mono
      (Filter.cocompact_le_cofinite : cocompact ℂ ≤ Filter.cofinite)
    simpa only [Metric.cobounded_eq_cocompact] using H
  have hfg : f =ᶠ[cobounded ℂ] (fun z => p.eval z / q.eval z) := by
    filter_upwards [hqevent] with z hz
    have hpA : AnalyticAt ℂ (fun w => p.eval w) z :=
      AnalyticOnNhd.eval_polynomial p z (mem_univ z)
    have hqA : AnalyticAt ℂ (fun w => q.eval w) z :=
      AnalyticOnNhd.eval_polynomial q z (mem_univ z)
    have H := (hf (mem_univ z)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      (hpA.div hqA hz).meromorphicNFAt
    exact (H.mp (heq z)).eq_of_nhds
  rcases rational_limit_at_infinity p q with ⟨c, hc⟩ | hc
  · exact Or.inl ⟨c, hc.congr' hfg.symm⟩
  · exact Or.inr (hc.congr' hfg.symm)

/-- Two sequences tending to infinity, one with escaping images and the
other with uniformly bounded images, rule out rationality. -/
theorem not_rational_meromorphic_of_two_sequences
    {f : ℂ → ℂ} (hf : MeromorphicNFOn f univ)
    (a b : ℕ → ℂ)
    (ha : Tendsto a atTop (cobounded ℂ))
    (hb : Tendsto b atTop (cobounded ℂ))
    (hfa : Tendsto (fun n => f (a n)) atTop (cobounded ℂ))
    (R : ℝ) (hfb : ∀ n, ‖f (b n)‖ ≤ R) :
    ¬ IsRationalMeromorphic f := by
  intro hr
  rcases rational_meromorphic_limit_at_infinity hf hr with ⟨c, hc⟩ | hc
  · have Htop := tendsto_norm_cobounded_atTop.comp hfa
    have Hfinite := (hc.comp ha).norm
    exact not_tendsto_nhds_of_tendsto_atTop Htop ‖c‖ Hfinite
  · have Htop := tendsto_norm_cobounded_atTop.comp (hc.comp hb)
    obtain ⟨n, hn⟩ := (Htop.eventually (eventually_gt_atTop R)).exists
    exact (not_lt_of_ge (hfb n)) hn

end FunctionTheory
