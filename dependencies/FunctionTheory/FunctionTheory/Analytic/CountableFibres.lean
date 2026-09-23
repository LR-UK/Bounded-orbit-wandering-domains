import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.DiscreteSubset
import Mathlib.Tactic

open Set Metric Filter Function
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- Every fibre of a nonconstant analytic function on a connected domain
is countable. The nonconstancy needed for this fibre is stated explicitly. -/
theorem countable_fibre_of_analyticOnNhd {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U) {b : ℂ}
    (hne : ∃ z∈U, f z≠b) : ({z | f z=b} ∩ U).Countable := by
  have hc : {z | f z≠b}∈codiscreteWithin U := by
    rcases (hf.sub analyticOnNhd_const).eqOn_zero_or_eventually_ne_zero_of_preconnected hU with h | h
    · obtain ⟨z,hz,hn⟩ := hne
      exact False.elim (hn (sub_eq_zero.mp (h hz)))
    · change ∀ᶠ z in codiscreteWithin U, f z≠b
      simpa only [Pi.sub_apply,Pi.zero_apply,sub_ne_zero] using h
  apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    (isDiscrete_of_codiscreteWithin _)
  simpa only [compl_setOf] using hc

/-- A nonconstant analytic map pulls countable sets back to countable sets
inside a connected domain. Two unequal values witness nonconstancy. -/
theorem countable_preimage_of_analyticOnNhd {f : ℂ → ℂ} {U S : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U) (hS : S.Countable)
    (hne : ∃ x∈U, ∃ y∈U, f x≠f y) : (U ∩ f ⁻¹' S).Countable := by
  obtain ⟨x,hx,y,hy,hxy⟩ := hne
  have hcount : ∀ b : ℂ, ({z | f z=b} ∩ U).Countable := by
    intro b
    apply countable_fibre_of_analyticOnNhd hf hU
    by_cases hb : f x=b
    · exact ⟨y,hy,fun H => hxy (hb.trans H.symm)⟩
    · exact ⟨x,hx,hb⟩
  have heq : U ∩ f ⁻¹' S=⋃ b∈S, ({z | f z=b} ∩ U) := by
    ext z
    simp only [mem_inter_iff,mem_preimage,mem_iUnion,mem_setOf_eq]
    constructor
    · intro hz
      exact ⟨f z,hz.2,rfl,hz.1⟩
    · rintro ⟨b,hb,hzb,hzU⟩
      exact ⟨hzU,hzb.symm ▸ hb⟩
  rw [heq]
  exact hS.biUnion (fun b _ => hcount b)

end FunctionTheory
