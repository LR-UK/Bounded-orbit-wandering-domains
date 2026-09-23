import FunctionTheory.Analytic.FiniteOrbitLocalDegree
import Mathlib.Data.Finset.Union
import Mathlib.Tactic

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- If a finite return map is locally nonconstant, then every one-step map
along that orbit is locally nonconstant. Analyticity is needed only along
the finite orbit, so this also applies at regular points of meromorphic maps. -/
theorem not_eventually_constant_at_orbit_point
    {f : ℂ → ℂ} {a : ℂ} {n : ℕ}
    (hf : ∀ j < n, AnalyticAt ℂ f (f^[j] a))
    (hnc : ¬ ∀ᶠ z in 𝓝 a, f^[n] z = f^[n] a)
    {j : ℕ} (hj : j < n) :
    ¬ ∀ᶠ z in 𝓝 (f^[j] a), f z = f (f^[j] a) := by
  intro h
  have hp : AnalyticAt ℂ (f^[j]) a :=
    analyticAt_iterate_of_finite_orbit (fun k hk => hf k (hk.trans hj))
  have heq : f =ᶠ[𝓝 (f^[j] a)] (fun _ => f (f^[j] a)) := h
  have H := heq.comp_tendsto hp.continuousAt
  have H' := H.fun_comp (f^[n-(j+1)])
  apply hnc
  filter_upwards [H'] with z hz
  change f^[n-(j+1)] (f (f^[j] z)) = f^[n-(j+1)] (f (f^[j] a)) at hz
  simpa only [← Function.iterate_succ_apply', ← Function.iterate_add_apply,
    Nat.sub_add_cancel (Nat.succ_le_of_lt hj)] using hz

/-- The finite set at which one-step Runge interpolation is required to
retain the marked data of a length-n return map. -/
noncomputable def finiteOrbitMarks (f : ℂ → ℂ) (C : Finset ℂ) (n : ℕ) : Finset ℂ := by
  classical
  exact (Finset.range n).biUnion (fun j => C.image (f^[j]))

theorem mem_finiteOrbitMarks {f : ℂ → ℂ} {C : Finset ℂ} {n : ℕ} {z : ℂ} :
    z ∈ finiteOrbitMarks f C n ↔ ∃ j < n, ∃ c ∈ C, f^[j] c = z := by
  classical
  simp only [finiteOrbitMarks, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]

/-- All finitely many interpolation sites are regular and locally
nonconstant whenever the marked return maps are regular and locally
nonconstant along their orbits. -/
theorem finiteOrbitMarks_analytic_and_nonconstant
    {f : ℂ → ℂ} {C : Finset ℂ} {n : ℕ}
    (hf : ∀ c ∈ C, ∀ j < n, AnalyticAt ℂ f (f^[j] c))
    (hnc : ∀ c ∈ C, ¬ ∀ᶠ z in 𝓝 c, f^[n] z = f^[n] c) :
    ∀ z ∈ finiteOrbitMarks f C n,
      AnalyticAt ℂ f z ∧ ¬ ∀ᶠ w in 𝓝 z, f w = f z := by
  intro z hz
  obtain ⟨j,hj,c,hc,rfl⟩ := mem_finiteOrbitMarks.mp hz
  exact ⟨hf c hc j hj,not_eventually_constant_at_orbit_point (hf c hc) (hnc c hc) hj⟩

end FunctionTheory
