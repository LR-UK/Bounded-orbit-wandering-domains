import ComplexApproximation.Topology.FullCompactSets
import FunctionTheory.Topology.LocallyFiniteCompactFamily

/-!
# Escaping families of full compact sets

The bounded-pieces criterion was first proved in the Eremenko application.
It is used here for locally finite disjoint compact families.
-/

open Set Filter Metric Bornology
open scoped Topology

namespace ComplexApproximation

theorem noBoundedComplementComponents_of_full_compact_pieces {E : Set ℂ}
    (hE : IsClosed E)
    (hpieces : ∀ R : ℝ, ∃ K : Set ℂ, IsCompact K ∧ IsConnected Kᶜ ∧
      K ⊆ E ∧ E ∩ closedBall 0 R ⊆ K) :
    ComplexApproximation.NoBoundedComplementComponents E := by
  intro z hz hb
  obtain ⟨R, hR, hbound⟩ := hb.closure.exists_pos_norm_le
  obtain ⟨K, hK, hfull, hKE, hEK⟩ := hpieces R
  obtain ⟨p, hpz, hpK⟩ := Runge.exists_polynomial_separator K hK hfull z (fun h => hz (hKE h))
  have hfront : frontier (connectedComponentIn Eᶜ z) ⊆ E := by
    simpa only [compl_compl] using frontier_component_subset_compl hE.isOpen_compl hz
  have hfrontK : frontier (connectedComponentIn Eᶜ z) ⊆ K := by
    intro w hw
    apply hEK
    refine ⟨hfront hw, ?_⟩
    simpa only [mem_closedBall, dist_zero_right] using hbound w hw.1
  have hn := Complex.norm_le_of_forall_mem_frontier_norm_le hb
    p.differentiable.diffContOnCl (fun w hw => (hpK w (hfrontK hw)).le)
    (subset_closure (mem_connectedComponentIn hz))
  rw [hpz, norm_one] at hn
  norm_num at hn


/-- A disjoint escaping family of full compact sets has no bounded
complementary components. -/
theorem noBoundedComplementComponents_escaping_full_family
    (K : ℕ → Set ℂ) (hK : ∀ n, IsCompact (K n))
    (hfull : ∀ n, IsConnected (K n)ᶜ)
    (hdis : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hescape : ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K n, R < ‖z‖) :
    NoBoundedComplementComponents (⋃ n, K n) := by
  apply noBoundedComplementComponents_of_full_compact_pieces
    ((FunctionTheory.locallyFinite_of_uniform_norm_escape K hescape).isClosed_iUnion
      (fun n => (hK n).isClosed))
  intro R
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hescape R)
  let A : Set ℂ := ⋃ n ∈ Finset.range N, K n
  refine ⟨A, (Finset.range N).isCompact_biUnion (fun n _ => hK n),
    isConnected_compl_finite_disjoint_union (Finset.range N) K
      (fun n _ => hK n) (fun n _ => hfull n) (fun i _ j _ hij => hdis hij), ?_, ?_⟩
  · intro z hz
    obtain ⟨n, _, hn⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion.mpr ⟨n, hn⟩
  · intro z hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp hz.1
    have hnorm : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz.2
    have hnN : n < N := by
      by_contra h
      exact (not_lt_of_ge hnorm) (hN n (by omega) z hn)
    exact mem_iUnion₂.mpr ⟨n, Finset.mem_range.mpr hnN, hn⟩

end ComplexApproximation
