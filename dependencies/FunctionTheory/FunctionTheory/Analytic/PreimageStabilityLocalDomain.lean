import FunctionTheory.Analytic.PreimageStability
import FunctionTheory.Analytic.OpenHolomorphic

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Compact preimage stability for open holomorphic functions defined only
on their working domain. No values outside that domain are part of the input. -/
theorem compact_preimage_density_on_domain
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f : U → ℂ} (hf : IsHolomorphicFunctionOn U f) (hopen : IsOpenMap f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (P : Set ℂ) (g : U → ℂ),
      (∀ a : U, (a : ℂ) ∈ K → infEDist (f a) P ≤ ENNReal.ofReal δ) →
      IsHolomorphicFunctionOn U g → (∀ z : U, ‖f z - g z‖ < δ) →
      ∀ a ∈ K, ∃ z : U, g z ∈ P ∧ dist a (z : ℂ) < ε := by
  have hnc : ∀ a ∈ K, ¬ ∀ᶠ z in 𝓝 a,
      domainExtension f z = domainExtension f a := by
    intro a ha
    simpa only [domainExtension_apply f a (hKU ha)] using
      (hf.isOpenMap_iff_locally_nonconstant hU).mp hopen ⟨a, hKU ha⟩
  obtain ⟨δ, hδ, H⟩ := compact_preimage_density_of_approximation hU hK hKU
    ((hf.differentiableOn_extension hU).analyticOnNhd hU) hnc hε
  refine ⟨δ, hδ, ?_⟩
  intro P g hP hg hclose a ha
  have hP' : ∀ a ∈ K, infEDist (domainExtension f a) P ≤ ENNReal.ofReal δ := by
    intro a ha
    simpa only [domainExtension_apply f a (hKU ha)] using hP ⟨a, hKU ha⟩ ha
  have hclose' : ∀ z ∈ U, ‖domainExtension f z - domainExtension g z‖ < δ := by
    intro z hz
    simpa only [domainExtension_apply f z hz, domainExtension_apply g z hz] using
      hclose ⟨z, hz⟩
  obtain ⟨z, hzU, hzP, hdist⟩ := H P (domainExtension g) hP'
    ((hg.differentiableOn_extension hU).analyticOnNhd hU) hclose' a ha
  exact ⟨⟨z, hzU⟩, by simpa only [domainExtension_apply g z hzU] using hzP, hdist⟩

end FunctionTheory
