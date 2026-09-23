import Mathlib.Analysis.Analytic.Order
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Matching one-step values on a finite reference orbit preserves all
iterates through its last point. -/
theorem iterate_eq_of_finite_orbit_values {α : Type*} {f g : α → α} {a : α}
    {N : ℕ} (hv : ∀ j < N, g (f^[j] a) = f (f^[j] a)) :
    ∀ j ≤ N, g^[j] a = f^[j] a := by
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih (by omega), hv j (by omega)]

/-- Analyticity along the finite orbit suffices for analyticity of the
iterate at its starting point. No global regularity is assumed. -/
theorem analyticAt_iterate_of_finite_orbit {f : ℂ → ℂ} {a : ℂ} {n : ℕ}
    (hf : ∀ j < n, AnalyticAt ℂ f (f^[j] a)) :
    AnalyticAt ℂ (f^[n]) a := by
  induction n with
  | zero => exact analyticAt_id
  | succ n ih =>
    have hn : AnalyticAt ℂ (f^[n]) a := ih (fun j hj => hf j (by omega))
    simpa only [Function.iterate_succ', Function.comp_def] using
      (hf n (by omega)).comp (f := f^[n]) (x := a) hn

/-- The centred local degree is multiplicative under composition. This
includes critical points and locally constant germs. -/
theorem centered_local_degree_comp {f g : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f (g a)) (hg : AnalyticAt ℂ g a) :
    analyticOrderAt (fun z => f (g z) - f (g a)) a =
      analyticOrderAt (fun z => f z - f (g a)) (g a) *
        analyticOrderAt (fun z => g z - g a) a := by
  have hF : AnalyticAt ℂ (fun w => f w - f (g a)) (g a) :=
    hf.sub analyticAt_const
  simpa only [Function.comp_def] using hF.analyticOrderAt_comp hg

/-- Finite interpolation of values and centred local degrees at every
intermediate orbit point preserves the value and local degree of the full
return map. This is the marked-point input for oscillating approximation. -/
theorem iterate_value_and_local_degree_eq_of_finite_orbit_data
    {f g : ℂ → ℂ} {a : ℂ} {n : ℕ}
    (hf : ∀ j < n, AnalyticAt ℂ f (f^[j] a))
    (hg : ∀ j < n, AnalyticAt ℂ g (f^[j] a))
    (hv : ∀ j < n, g (f^[j] a) = f (f^[j] a))
    (hd : ∀ j < n,
      analyticOrderAt (fun z => g z - g (f^[j] a)) (f^[j] a) =
        analyticOrderAt (fun z => f z - f (f^[j] a)) (f^[j] a)) :
    g^[n] a = f^[n] a ∧
      analyticOrderAt (fun z => g^[n] z - g^[n] a) a =
        analyticOrderAt (fun z => f^[n] z - f^[n] a) a := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have hvals := iterate_eq_of_finite_orbit_values hv
    have hvaln : g^[n] a = f^[n] a := hvals n (by omega)
    obtain ⟨_, hdn⟩ := ih (fun j hj => hf j (by omega))
      (fun j hj => hg j (by omega)) (fun j hj => hv j (by omega))
      (fun j hj => hd j (by omega))
    have hFn : AnalyticAt ℂ (f^[n]) a := analyticAt_iterate_of_finite_orbit (fun j hj => hf j (by omega))
    have hGn : AnalyticAt ℂ (g^[n]) a := by
      apply analyticAt_iterate_of_finite_orbit
      intro j hj
      rw [hvals j (by omega)]
      exact hg j (by omega)
    have hglast : AnalyticAt ℂ g (g^[n] a) := hvaln.symm ▸ hg n (by omega)
    refine ⟨hvals (n+1) le_rfl, ?_⟩
    simp only [Function.iterate_succ_apply']
    rw [centered_local_degree_comp hglast hGn,
      centered_local_degree_comp (hf n (by omega)) hFn,
      hdn, hvaln, hd n (by omega)]

end FunctionTheory
