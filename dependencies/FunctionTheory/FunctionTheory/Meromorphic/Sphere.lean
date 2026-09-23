import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

open Set Filter
open scoped Topology OnePoint

namespace FunctionTheory

set_option autoImplicit false

/-- Mathlib's normal-form representative agrees on a full neighbourhood
wherever the original representative was holomorphic. -/
theorem normal_meromorphic_representative_germ
    {f : ℂ → ℂ} (hf : MeromorphicOn f univ) {a : ℂ} (ha : AnalyticAt ℂ f a) :
    toMeromorphicNFOn f univ =ᶠ[𝓝 a] f := by
  have H := toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hf (mem_univ a)
  rwa [toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt] at H

/-- Every globally meromorphic representative has a normal representative
that retains all its holomorphic germs. -/
theorem exists_normal_meromorphic_representative
    {f : ℂ → ℂ} (hf : MeromorphicOn f univ) :
    ∃ g : ℂ → ℂ, MeromorphicNFOn g univ ∧
      (∀ a, g =ᶠ[𝓝[≠] a] f) ∧
      ∀ a, AnalyticAt ℂ f a → g =ᶠ[𝓝 a] f := by
  exact ⟨toMeromorphicNFOn f univ, meromorphicNFOn_toMeromorphicNFOn f univ,
    fun a => hf.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ a),
    fun _ ha => normal_meromorphic_representative_germ hf ha⟩

/-- The genuine sphere value of a normal meromorphic representative. Its
default complex value at a pole is replaced by infinity. -/
noncomputable def meromorphicSphereValue (f : ℂ → ℂ) (z : ℂ) : OnePoint ℂ := by
  classical
  exact if AnalyticAt ℂ f z then (f z : OnePoint ℂ) else ∞

theorem meromorphicSphereValue_of_analytic {f : ℂ → ℂ} {z : ℂ}
    (hz : AnalyticAt ℂ f z) : meromorphicSphereValue f z = (f z : OnePoint ℂ) := by
  simp only [meromorphicSphereValue, if_pos hz]

theorem meromorphicSphereValue_of_not_analytic {f : ℂ → ℂ} {z : ℂ}
    (hz : ¬ AnalyticAt ℂ f z) : meromorphicSphereValue f z = ∞ := by
  simp only [meromorphicSphereValue, if_neg hz]

/-- A globally meromorphic function in normal form defines a continuous
sphere-valued function, including at its poles. -/
theorem continuous_meromorphicSphereValue
    {f : ℂ → ℂ} (hf : MeromorphicNFOn f univ) :
    Continuous (meromorphicSphereValue f) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  by_cases ha : AnalyticAt ℂ f a
  · have he : meromorphicSphereValue f =ᶠ[𝓝 a] (fun z => (f z : OnePoint ℂ)) := by
      filter_upwards [(isOpen_analyticAt ℂ f).mem_nhds ha] with z hz
      exact meromorphicSphereValue_of_analytic hz
    exact (OnePoint.continuous_coe.continuousAt.comp ha.continuousAt).congr_of_eventuallyEq he
  · have hpole : meromorphicOrderAt f a < 0 :=
      ((meromorphicNFAt_iff_analyticAt_or.mp (hf (mem_univ a))).resolve_left ha).2.1
    have hescape : Tendsto f (𝓝[≠] a) (coclosedCompact ℂ) := by
      simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
        tendsto_cobounded_of_meromorphicOrderAt_neg hpole
    have H : Tendsto (fun z => (f z : OnePoint ℂ)) (𝓝[≠] a) (𝓝 (∞ : OnePoint ℂ)) :=
      OnePoint.tendsto_coe_infty.comp hescape
    have he : (fun z => (f z : OnePoint ℂ)) =ᶠ[𝓝[≠] a] meromorphicSphereValue f := by
      filter_upwards [hf.meromorphicOn.eventually_analyticAt_or_mem_compl (mem_univ a)]
        with z hz
      rcases hz with hz | hz
      · exact (meromorphicSphereValue_of_analytic hz).symm
      · exact (hz (mem_univ z)).elim
    apply continuousAt_iff_punctured_nhds.mpr
    rw [meromorphicSphereValue_of_not_analytic ha]
    exact H.congr' he

end FunctionTheory
