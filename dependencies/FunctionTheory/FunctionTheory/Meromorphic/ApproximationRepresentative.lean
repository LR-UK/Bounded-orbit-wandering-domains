import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- For continuous germs, agreement off the centre also gives agreement at
the centre, hence agreement on a full neighbourhood. -/
theorem eventuallyEq_of_punctured_eq_of_continuousAt
    {f g : ℂ → ℂ} {a : ℂ} (hf : ContinuousAt f a) (hg : ContinuousAt g a)
    (hfg : f =ᶠ[𝓝[≠] a] g) : f =ᶠ[𝓝 a] g := by
  have Hf : Tendsto f (𝓝[≠] a) (𝓝 (f a)) := hf.mono_left nhdsWithin_le_nhds
  have Hg : Tendsto g (𝓝[≠] a) (𝓝 (g a)) := hg.mono_left nhdsWithin_le_nhds
  have Hg' : Tendsto f (𝓝[≠] a) (𝓝 (g a)) := (tendsto_congr' hfg).mpr Hg
  have ha : f a = g a := tendsto_nhds_unique Hf Hg'
  have H := eventually_nhdsWithin_iff.mp hfg
  filter_upwards [H] with z hz
  by_cases hza : z = a
  · simpa only [hza] using ha
  · exact hz hza

/-- Choose values at the poles so that a principal-part-preserving
approximation has its analytic error on full neighbourhoods, including at
the poles. The resulting meromorphic map has exactly the same punctured
germs as the original approximant. -/
theorem exists_meromorphic_approximation_representative
    {K : Set ℂ} (hK : IsClosed K) (f r e : ℂ → ℂ)
    (hr : MeromorphicOn r univ) (he : AnalyticOnNhd ℂ e K)
    (herr : ∀ a ∈ K, (fun z => f z - r z) =ᶠ[𝓝[≠] a] e) :
    ∃ g : ℂ → ℂ,
      MeromorphicOn g univ ∧
      (∀ a ∈ K, (fun z => f z - g z) =ᶠ[𝓝 a] e) ∧
      AnalyticOnNhd ℂ (fun z => f z - g z) K ∧
      (∀ a, g =ᶠ[𝓝[≠] a] r) ∧
      EqOn g r Kᶜ ∧
      ∀ a ∈ K, AnalyticAt ℂ f a → AnalyticAt ℂ g a := by
  classical
  let g : ℂ → ℂ := fun z => if z ∈ K then f z - e z else r z
  have hgr : ∀ a, g =ᶠ[𝓝[≠] a] r := by
    intro a
    by_cases ha : a ∈ K
    · filter_upwards [herr a ha] with z hz
      by_cases hzK : z ∈ K
      · dsimp only [g]
        rw [if_pos hzK]
        linear_combination hz
      · simp only [g, if_neg hzK]
    · have H : g =ᶠ[𝓝 a] r := by
        filter_upwards [hK.isOpen_compl.mem_nhds ha] with z hz
        simp only [g, if_neg hz]
      exact H.filter_mono nhdsWithin_le_nhds
  have hlocal : ∀ a ∈ K, (fun z => f z - g z) =ᶠ[𝓝 a] e := by
    intro a ha
    have H := eventually_nhdsWithin_iff.mp (herr a ha)
    filter_upwards [H] with z hz
    by_cases hzK : z ∈ K
    · simp only [g, if_pos hzK]
      ring
    · have hza : z ≠ a := by intro h; subst z; exact hzK ha
      simpa only [g, if_neg hzK] using hz hza
  refine ⟨g, (fun a _ => (hr a (mem_univ a)).congr (hgr a).symm),
    hlocal, (fun a ha => (he a ha).congr (hlocal a ha).symm), hgr,
    (fun z hz => if_neg hz), ?_⟩
  intro a ha hfa
  have H : (fun z => f z - e z) =ᶠ[𝓝 a] g := by
    filter_upwards [hlocal a ha] with z hz
    linear_combination hz
  exact (hfa.sub (he a ha)).congr H

end FunctionTheory
