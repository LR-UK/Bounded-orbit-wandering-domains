import FunctionTheory.Conformal.StripProper
import Mathlib.Topology.OpenPartialHomeomorph.Basic

open Set Metric Filter
open scoped Topology

namespace FunctionTheory

/-- A conformal chart asymptotic to a translation has a uniformly continuous
inverse on every closed inset with bounded left truncations. -/
theorem uniformContinuousOn_inverse_of_strip_translation_limit
    (e : OpenPartialHomeomorph ℂ ℂ) {S : Set ℂ} {c : ℂ} {L M : ℝ}
    (hS : IsClosed S) (hSU : S ⊆ e.source)
    (hleft : ∀ z ∈ S, L ≤ z.re) (him : ∀ z ∈ S, |z.im| ≤ M)
    (hlim : Tendsto (fun z => e z - z) (comap Complex.re atTop ⊓ 𝓟 S) (𝓝 c)) :
    UniformContinuousOn e.symm (e '' S) := by
  have he : ContinuousOn e S := e.continuousOn.mono hSU
  obtain ⟨B, _, hB⟩ := exists_norm_bound_of_strip_limit hS hleft him
    (he.sub continuous_id.continuousOn) hlim
  have hclosed := isClosed_image_of_strip_translation_limit hS hleft him he hlim
  have hre : ∀ z ∈ S, |(e z).re - z.re| ≤ B := by
    intro z hz
    have h : |(e z).re - z.re| ≤ ‖e z - z‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (e z - z)
    exact h.trans (hB z hz)
  have himageL : ∀ w ∈ e '' S, L - B ≤ w.re := by
    rintro _ ⟨z, hz, rfl⟩
    have hd := (abs_le.mp (hre z hz)).1
    linarith [hleft z hz]
  have himageM : ∀ w ∈ e '' S, |w.im| ≤ M + B := by
    rintro _ ⟨z, hz, rfl⟩
    have hd : |(e z).im - z.im| ≤ B := by
      have h : |(e z).im - z.im| ≤ ‖e z - z‖ := by
        simpa only [Complex.sub_im] using Complex.abs_im_le_norm (e z - z)
      exact h.trans (hB z hz)
    have hh := abs_add_le ((e z).im - z.im) z.im
    rw [sub_add_cancel] at hh
    linarith [him z hz]
  have htarget : e '' S ⊆ e.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_source (hSU hz)
  have hi : Tendsto (fun w => e.symm w - w)
      (comap Complex.re atTop ⊓ 𝓟 (e '' S)) (𝓝 (-c)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hev := hlim.eventually (ball_mem_nhds c hε)
    obtain ⟨R, hR⟩ := eventually_atTop.mp
      (eventually_comap.mp (eventually_inf_principal.mp hev))
    apply eventually_inf_principal.mpr
    apply eventually_comap.mpr
    apply eventually_atTop.mpr
    refine ⟨R + B, ?_⟩
    intro t ht w hwt hw
    obtain ⟨z, hz, rfl⟩ := hw
    have hzR : R ≤ z.re := by
      have hb := (abs_le.mp (hre z hz)).2
      rw [← hwt] at ht
      linarith
    have hh : dist (e z - z) c < ε := hR z.re hzR z rfl hz
    rw [e.left_inv (hSU hz)]
    rw [dist_eq_norm] at hh ⊢
    have hneg : z - e z - -c = -(e z - z - c) := by ring
    rwa [hneg, norm_neg]
  exact uniformContinuousOn_of_strip_translation_limit hclosed himageL himageM
    (e.continuousOn_symm.mono htarget) hi

end FunctionTheory
