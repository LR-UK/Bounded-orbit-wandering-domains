import FunctionTheory.Topology.FiniteComposition
import FunctionTheory.Holomorphic

open Set Metric

namespace FunctionTheory

set_option autoImplicit false

/-- Finite composition stability for functions on their actual open domains.
The internal extensions are used only at points proved to lie in those domains. -/
theorem finiteComposition_approximation_on_domains
    (U : ℕ → Set ℂ) (g : ∀ k, U k → ℂ) (K : Set ℂ) (hK : IsCompact K) (n : ℕ)
    (hU : ∀ k < n, IsOpen (U k)) (hg : ∀ k < n, Continuous (g k))
    (horbit : ∀ k < n,
      MapsTo (finiteComposition (fun j => domainExtension (g j)) k) K (U k))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ f : ∀ k, U k → ℂ,
      (∀ k < n, ∀ z : U k, dist (f k z) (g k z) < δ) →
      (∀ k ≤ n, ∀ z ∈ K,
        dist (finiteComposition (fun j => domainExtension (f j)) k z)
          (finiteComposition (fun j => domainExtension (g j)) k z) < ε) ∧
      (∀ k < n,
        MapsTo (finiteComposition (fun j => domainExtension (f j)) k) K (U k)) := by
  have hg' : ∀ k < n, ContinuousOn (domainExtension (g k)) (U k) := by
    intro k hk
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : (fun z : U k => domainExtension (g k) z) = g k := by
      funext z
      exact domainExtension_apply (g k) z z.property
    change Continuous (fun z : U k => domainExtension (g k) z)
    rw [heq]
    exact hg k hk
  obtain ⟨δ, hδ, H⟩ := finiteComposition_approximation_on_compact
    (fun j => domainExtension (g j)) U K hK n hU hg' horbit ε hε
  refine ⟨δ, hδ, fun f hf => H (fun j => domainExtension (f j)) ?_⟩
  intro k hk z hz
  simpa only [domainExtension_apply (f k) z hz, domainExtension_apply (g k) z hz]
    using hf k hk ⟨z, hz⟩

end FunctionTheory
