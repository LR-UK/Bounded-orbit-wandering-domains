import EremenkosConjecture.WadaFilled
import EremenkosConjecture.FastEscape

open Set Metric Function ComplexDynamics

namespace EremenkosConjecture

/-- The topological existence result used in Section 3, proved by the lake construction. -/
theorem exists_countably_many_lakes_of_wada :
    ∃ X : Set ℂ, ∃ U : ℕ → Set ℂ, IsCompact X ∧ IsConnected X ∧ Injective U ∧
      Pairwise (Disjoint on U) ∧
      ∀ i, IsOpen (U i) ∧ IsConnected (U i) ∧ Bornology.IsBounded (U i) ∧ frontier (U i) = X := by
  obtain ⟨W⟩ := exists_wadaConstruction
  refine ⟨W.boundary, fun i => W.domain (some i), W.compact_boundary, W.connected_boundary,
    W.injective_domains, ?_, ?_⟩
  · intro i j hij
    exact W.disjoint_domains (fun H => hij (Option.some.inj H))
  · intro i
    exact ⟨W.open_domain _, W.connected_domain _, W.bounded_domain _, W.frontier_domain _⟩

/-- **Theorem 1.4, as proved in Section 3.** Infinitely many wandering Fatou domains
share a compact connected boundary. The domains and their boundaries may all be
chosen fast escaping. -/
theorem wandering_lakes_of_wada :
    ∃ f : ℂ → ℂ, ∃ X : Set ℂ, ∃ U : ℕ → Set ℂ,
      IsTranscendentalEntire f ∧ IsCompact X ∧ IsConnected X ∧ X ⊆ juliaSet f ∧
      Injective U ∧ Pairwise (Disjoint on U) ∧
      ∀ i, IsWanderingDomain f (U i) ∧ frontier (U i) = X ∧
        closure (U i) ⊆ fastEscapingSet f ∧ EscapesUniformlyOn f (closure (U i)) := by
  obtain ⟨W⟩ := exists_wadaConstruction
  obtain ⟨f, hf, _, hescape, hJulia, hwander, hfast, _⟩ :=
    fast_escaping_wandering_compactum W.filled W.compact_filled W.full_filled
  refine ⟨f, W.boundary, fun i => W.domain (some i), hf, W.compact_boundary,
    W.connected_boundary, ?_, W.injective_domains, ?_, ?_⟩
  · rwa [W.frontier_filled] at hJulia
  · intro i j hij
    exact W.disjoint_domains (fun H => hij (Option.some.inj H))
  · intro i
    obtain ⟨x, hx⟩ := (W.connected_domain (some i)).nonempty
    have hwand := hwander x (W.domain_subset_interior_filled i hx)
    rw [W.connectedComponentIn_interior_filled i hx] at hwand
    have hcl : closure (W.domain (some i)) ⊆ W.filled :=
      closure_minimal (W.domain_subset_filled i) W.compact_filled.isClosed
    exact ⟨hwand, W.frontier_domain _, hcl.trans hfast, hescape.mono hcl⟩

/-- An infinite indexed collection of distinct Fatou components with one common boundary. -/
theorem fatou_components_common_boundary :
    ∃ f : ℂ → ℂ, ∃ X : Set ℂ, ∃ U : ℕ → Set ℂ,
      IsTranscendentalEntire f ∧ IsCompact X ∧ IsConnected X ∧ Injective U ∧
      ∀ i, IsFatouComponent f (U i) ∧ frontier (U i) = X := by
  obtain ⟨f, X, U, hf, hXc, hXconn, _, hU, _, hdomains⟩ := wandering_lakes_of_wada
  exact ⟨f, X, U, hf, hXc, hXconn, hU, fun i => ⟨(hdomains i).1.1, (hdomains i).2.1⟩⟩

end EremenkosConjecture
