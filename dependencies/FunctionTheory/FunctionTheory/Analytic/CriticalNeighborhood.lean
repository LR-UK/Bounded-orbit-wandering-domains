import FunctionTheory.Analytic.CompactCriticalPoints
import Mathlib.Topology.Separation.Regular

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Critical-point control on a compact set extends to a relatively compact
open neighbourhood when the holomorphic germs are locally nonconstant.
The neighbourhood can be chosen with no additional critical points even
on its closure. -/
theorem exists_critical_control_neighborhood
    {K U C : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hnc : ∀ a ∈ K, ¬ ∀ᶠ z in 𝓝 a, f z = f a)
    (hcritical : ∀ a ∈ K, deriv f a = 0 → a ∈ C) :
    ∃ W, IsOpen W ∧ K ⊆ W ∧ closure W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ z ∈ closure W, deriv f z = 0 → z ∈ C := by
  let P : Set ℂ := {z | z ∈ U ∧ (deriv f z = 0 → z ∈ C)}
  have hKP : K ⊆ interior P := by
    intro a ha
    have hfinite : analyticOrderAt (deriv f) a ≠ ⊤ := by
      intro htop
      have h := (hf a (hKU ha)).analyticOrderAt_deriv_add_one
      rw [htop, top_add] at h
      apply hnc a ha
      filter_upwards [analyticOrderAt_eq_top.mp h.symm] with z hz
      exact sub_eq_zero.mp hz
    have hne : ∀ᶠ z in 𝓝[≠] a, deriv f z ≠ 0 := by
      rcases (hf a (hKU ha)).deriv.eventually_eq_zero_or_eventually_ne_zero with hz | hz
      · exact (hfinite (analyticOrderAt_eq_top.mpr hz)).elim
      · exact hz
    have hne' : ∀ᶠ z in 𝓝 a, z ≠ a → deriv f z ≠ 0 := by
      simpa only [mem_compl_iff, mem_singleton_iff] using eventually_nhdsWithin_iff.mp hne
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hU.mem_nhds (hKU ha), hne'] with z hzU hz
    refine ⟨hzU, ?_⟩
    intro hdz
    by_cases hza : z = a
    · subst z
      exact hcritical a ha hdz
    · exact (hz hza hdz).elim
  obtain ⟨W, hW, hKW, hWP, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK isOpen_interior hKP
  exact ⟨W, hW, hKW, fun z hz => (interior_subset (hWP hz)).1, hWc,
    fun z hz => (interior_subset (hWP hz)).2⟩

end FunctionTheory
