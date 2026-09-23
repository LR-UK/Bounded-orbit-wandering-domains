import FunctionTheory.Analytic.FiniteInterpolation
import Mathlib.Topology.DiscreteSubset

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- A locally nonconstant analytic function has only finitely many critical points
in a compact subset of its domain. No connectedness of the domain is required. -/
theorem finite_critical_points_of_locally_nonconstant
    {K : Set ℂ} (hK : IsCompact K) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f K)
    (hnc : ∀ a ∈ K, ¬ ∀ᶠ z in 𝓝 a, f z = f a) :
    {a ∈ K | deriv f a = 0}.Finite := by
  have hcod : ∀ᶠ a in codiscreteWithin K, deriv f a ≠ 0 := by
    rw [eventually_codiscreteWithin_iff_forall_eventually_nhdsNE]
    intro a ha
    have horder : analyticOrderAt (deriv f) a ≠ ⊤ := by
      intro htop
      have h := (hf a ha).analyticOrderAt_deriv_add_one
      rw [htop, top_add] at h
      have he := analyticOrderAt_eq_top.mp h.symm
      apply hnc a ha
      filter_upwards [he] with z hz
      exact sub_eq_zero.mp hz
    rcases (hf a ha).deriv.eventually_eq_zero_or_eventually_ne_zero with hz | hn
    · exact False.elim (horder (analyticOrderAt_eq_top.mpr hz))
    · exact hn.mono (fun z hz _ => hz)
  have hfinite := hK.finite_sdiff_of_mem_codiscreteWithin hcod
  convert hfinite using 1
  ext a
  simp

end FunctionTheory
