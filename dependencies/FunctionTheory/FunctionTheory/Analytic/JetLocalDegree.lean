import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Matching the jet through the first nonzero derivative preserves a finite
analytic order of vanishing. -/
theorem analyticOrderAt_eq_of_equal_jets
    {f g : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a)
    (d : ℕ) (hd : analyticOrderAt f a = d)
    (hjet : ∀ k ≤ d, iteratedDeriv k f a = iteratedDeriv k g a) :
    analyticOrderAt g a = analyticOrderAt f a := by
  rw [hd]
  obtain ⟨Hzero, Hnz⟩ := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf).mp hd
  apply (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hg).mpr
  refine ⟨?_, ?_⟩
  · intro k hk
    rw [← hjet k hk.le]
    exact Hzero k hk
  · rwa [← hjet d le_rfl]

/-- Matching values and derivatives through the centred local degree
preserves that degree, including at critical points. -/
theorem centered_local_degree_eq_of_equal_jets
    {f g : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a)
    (d : ℕ) (hd : analyticOrderAt (fun z => f z - f a) a = d)
    (hjet : ∀ k ≤ d, iteratedDeriv k f a = iteratedDeriv k g a) :
    analyticOrderAt (fun z => g z - g a) a =
      analyticOrderAt (fun z => f z - f a) a := by
  have ha : f a = g a := by simpa only [iteratedDeriv_zero] using hjet 0 (Nat.zero_le d)
  apply analyticOrderAt_eq_of_equal_jets (hf.sub analyticAt_const)
    (hg.sub analyticAt_const) d hd
  intro k hk
  change iteratedDeriv k (fun z => f z - f a) a =
    iteratedDeriv k (fun z => g z - g a) a
  rw [iteratedDeriv_fun_sub hf.contDiffAt analyticAt_const.contDiffAt,
    iteratedDeriv_fun_sub hg.contDiffAt analyticAt_const.contDiffAt, hjet k hk, ha]

/-- Every locally nonconstant holomorphic germ needs only a finite jet to
preserve its value and its centred local degree. -/
theorem exists_jet_order_preserving_value_and_local_degree
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a)
    (hnc : ¬ ∀ᶠ z in 𝓝 a, f z = f a) :
    ∃ m : ℕ, 0 < m ∧ ∀ g : ℂ → ℂ, AnalyticAt ℂ g a →
      (∀ k < m, iteratedDeriv k f a = iteratedDeriv k g a) →
      g a = f a ∧ analyticOrderAt (fun z => g z - g a) a =
        analyticOrderAt (fun z => f z - f a) a := by
  have hfinite : analyticOrderAt (fun z => f z - f a) a ≠ ⊤ := by
    intro H
    apply hnc
    filter_upwards [analyticOrderAt_eq_top.mp H] with z hz
    exact sub_eq_zero.mp hz
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hfinite
  refine ⟨d + 1, by omega, ?_⟩
  intro g hg hj
  refine ⟨?_, centered_local_degree_eq_of_equal_jets hf hg d hd.symm
    (fun k hk => hj k (by omega))⟩
  simpa only [iteratedDeriv_zero] using (hj 0 (by omega)).symm

end FunctionTheory
