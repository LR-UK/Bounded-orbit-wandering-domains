import TauCeti.Analysis.Complex.Conformal.LocalDegree
import Mathlib.Topology.UniformSpace.Compact

open Set Filter Metric
open scoped Topology Uniformity

namespace FunctionTheory

set_option autoImplicit false

/-- Local injectivity near a compact set admits a common radius, with all
balls kept inside the prescribed domain. -/
theorem exists_uniform_injective_radius
    {X Y : Type*} [MetricSpace X] {K U : Set X} (hK : IsCompact K) {f : X → Y}
    (hloc : ∀ a ∈ K, ∃ S ∈ 𝓝 a, S ⊆ U ∧ InjOn f S) :
    ∃ r > 0, ∀ a ∈ K, ball a r ⊆ U ∧ InjOn f (ball a r) := by
  classical
  have hloc' : ∀ a : K, ∃ S ∈ 𝓝 (a : X), S ⊆ U ∧ InjOn f S :=
    fun a => hloc a a.property
  choose S hS hSU hinj using hloc'
  obtain ⟨W, hW, H⟩ := lebesgue_number_lemma_nhds' hK (fun a ha => hS ⟨a, ha⟩)
  obtain ⟨r, hr, hrW⟩ := Metric.mem_uniformity_dist.mp hW
  refine ⟨r, hr, ?_⟩
  intro a ha
  obtain ⟨b, hb⟩ := H a ha
  have hsub : ball a r ⊆ S b := by
    intro z hz
    apply hb
    apply hrW
    simpa only [mem_ofPred_eq, dist_comm] using mem_ball.mp hz
  exact ⟨hsub.trans (hSU b), (hinj b).mono hsub⟩

/-- A holomorphic map with nonzero derivative on a compact set is injective
on uniformly sized balls about its points. The balls lie inside its domain. -/
theorem exists_uniform_injective_radius_of_deriv_ne_zero
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hd : ∀ a ∈ K, deriv f a ≠ 0) :
    ∃ r > 0, ∀ a ∈ K, ball a r ⊆ U ∧ InjOn f (ball a r) := by
  apply exists_uniform_injective_radius hK
  intro a ha
  obtain ⟨S, hS, hSi⟩ := (TauCeti.exists_injOn_nhds_iff_deriv_ne_zero
    (hf a (hKU ha))).mpr (hd a ha)
  exact ⟨S ∩ U, inter_mem hS (hU.mem_nhds (hKU ha)), inter_subset_right,
    hSi.mono inter_subset_left⟩

end FunctionTheory
