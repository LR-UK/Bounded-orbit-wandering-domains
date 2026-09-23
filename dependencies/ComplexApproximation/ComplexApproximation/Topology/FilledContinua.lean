import ComplexApproximation.Topology.Filling
import ComplexApproximation.Topology.Nonseparation
import TauCeti.Analysis.Normed.Module.FilledHull
import Mathlib.Topology.Connected.Clopen

/-! # Filling compact continua

Filling all bounded complementary components preserves compactness and
connectedness. The filled compactum is full. If the ambient domain has a
connected unbounded complement, the filling remains in that domain.
-/

open Set Metric Bornology

namespace ComplexApproximation

theorem isCompact_fill {K : Set ℂ} (hK : IsCompact K) : IsCompact (fill K) := by
  apply isCompact_iff_isClosed_bounded.mpr
  refine ⟨isClosed_fill hK.isClosed, ?_⟩
  change IsBounded (TauCeti.filledHull K)
  exact TauCeti.isBounded_filledHull.mpr hK.isBounded

theorem isConnected_compl_fill {K : Set ℂ} (hK : IsCompact K) :
    IsConnected (fill K)ᶜ :=
  isConnected_compl_of_unbounded_components _ (isCompact_fill hK).isBounded
    (noBoundedComplementComponents_fill K)

theorem isConnected_fill {K : Set ℂ} (hK : IsClosed K) (hconn : IsConnected K) :
    IsConnected (fill K) := by
  obtain ⟨a, ha⟩ := hconn.nonempty
  refine ⟨⟨a, subset_fill K ha⟩, isPreconnected_of_forall a ?_⟩
  intro z hz
  by_cases hzK : z ∈ K
  · exact ⟨K, subset_fill K, ha, hzK, hconn.isPreconnected⟩
  let C := connectedComponentIn Kᶜ z
  have hzC : z ∈ C := mem_connectedComponentIn hzK
  have hCconn : IsConnected C := isConnected_connectedComponentIn_iff.mpr hzK
  have hCne : C ≠ univ := by
    intro h
    have haC : a ∈ C := h.symm ▸ mem_univ a
    exact connectedComponentIn_subset Kᶜ z haC ha
  obtain ⟨b, hb⟩ := nonempty_frontier_iff.mpr ⟨⟨z, hzC⟩, hCne⟩
  have hbK : b ∈ K := by
    simpa only [compl_compl] using
      frontier_component_subset_compl hK.isOpen_compl hzK hb
  have hCfill : C ⊆ fill K := by
    intro w hw
    change IsBounded (connectedComponentIn Kᶜ w)
    exact (connectedComponentIn_eq hw) ▸ hz
  have hclfill : closure C ⊆ fill K := closure_minimal hCfill (isClosed_fill hK)
  exact ⟨K ∪ closure C, union_subset (subset_fill K) hclfill,
    Or.inl ha, Or.inr (subset_closure hzC),
    (hconn.union ⟨b, hbK, hb.1⟩ hCconn.closure).isPreconnected⟩

theorem fill_subset_of_unbounded_preconnected_complement {K U : Set ℂ}
    (hKU : K ⊆ U) (hUc : IsPreconnected Uᶜ) (hUu : ¬ IsBounded Uᶜ) :
    fill K ⊆ U := by
  intro z hz
  by_contra hzU
  change IsBounded (connectedComponentIn Kᶜ z) at hz
  have hsub := hUc.subset_connectedComponentIn hzU (compl_subset_compl.mpr hKU)
  exact hUu (hz.subset hsub)

theorem fill_subset_of_noBoundedComplementComponents {K U : Set ℂ}
    (hKU : K ⊆ U) (hU : NoBoundedComplementComponents U) : fill K ⊆ U := by
  simpa only [fill_eq_self hU] using fill_mono hKU

end ComplexApproximation
