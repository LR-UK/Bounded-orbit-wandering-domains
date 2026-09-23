import EremenkosConjecture.PlaneTopology
import Runge.PolynomialSeparation
import ComplexApproximation.Topology.Arakelian

/-! # Ruling out holes using full compact pieces

This criterion is useful for unbounded unions of strips: each bounded part
must lie in a full compact subset of the union. The argument uses polynomial
separation on the boundary of a hypothetical bounded hole.
-/

open Set Metric Bornology

namespace EremenkosConjecture

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

end EremenkosConjecture
