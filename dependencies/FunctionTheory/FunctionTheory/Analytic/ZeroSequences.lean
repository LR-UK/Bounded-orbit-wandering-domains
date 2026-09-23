import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.MeanValue

/-! # Distinct zeros of a nonzero entire function escape every compact set -/

open Filter Set Function Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

theorem tendsto_norm_atTop_of_injective_zeros {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g univ) (hne : ∃ z, g z ≠ 0)
    (u : ℕ → ℂ) (hu : Injective u) (hzero : ∀ n, g (u n) = 0) :
    Tendsto (fun n => ‖u n‖) atTop atTop := by
  have hcod : ∀ᶠ z in codiscreteWithin (univ : Set ℂ), g z ≠ 0 := by
    rcases hg.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with h | h
    · obtain ⟨z, hz⟩ := hne
      exact False.elim (hz (h (mem_univ z)))
    · exact h
  apply Filter.tendsto_atTop.2
  intro R
  have hc : {z : ℂ | g z ≠ 0} ∈ codiscreteWithin (closedBall 0 R) :=
    codiscreteWithin_mono (subset_univ _) hcod
  have hs := (isCompact_closedBall (0 : ℂ) R).finite_sdiff_of_mem_codiscreteWithin hc
  have he : ∀ᶠ n : ℕ in cofinite,
      u n ∉ closedBall 0 R \ {z : ℂ | g z ≠ 0} :=
    hu.tendsto_cofinite.eventually hs.compl_mem_cofinite
  have he' : ∀ᶠ n : ℕ in atTop,
      u n ∉ closedBall 0 R \ {z : ℂ | g z ≠ 0} := by
    simpa only [Nat.cofinite_eq_atTop] using he
  filter_upwards [he'] with n hn
  have hnot : u n ∉ closedBall 0 R := by
    intro hmem
    exact hn ⟨hmem, by simp [hzero n]⟩
  have : R < ‖u n‖ := by simpa using hnot
  exact this.le

/-- A sequence of distinct critical points of a nonconstant entire map escapes. -/
theorem tendsto_norm_atTop_of_injective_critical_points {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : ∃ z w, f z ≠ f w)
    (u : ℕ → ℂ) (hu : Injective u) (hcrit : ∀ n, deriv f (u n) = 0) :
    Tendsto (fun n => ‖u n‖) atTop atTop := by
  apply tendsto_norm_atTop_of_injective_zeros
    (fun z _ => (hf.analyticAt z).deriv) ?_ u hu hcrit
  by_contra! h
  obtain ⟨z, w, hzw⟩ := hne
  exact hzw (is_const_of_deriv_eq_zero hf h z w)

end FunctionTheory
