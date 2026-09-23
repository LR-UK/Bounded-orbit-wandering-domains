import EremenkosConjecture.ConstructionData
import EremenkosConjecture.BoundarySelection

/-! # Choosing nested compacta and boundary points inside the unit disk -/

open Set Metric Filter
open scoped Topology

namespace EremenkosConjecture

theorem exists_uniformEscapeData (K : Set ℂ) (hK : IsCompact K)
    (hfull : IsConnected Kᶜ) (hnorm : K ⊆ targetDisc 0) :
    ∃ D : UniformEscapeData, (∀ n, K ⊆ D.K n) ∧
      (⋂ n, D.K n) = K ∧ frontier K ⊆ closure (⋃ n, D.P n) := by
  classical
  obtain ⟨L, hL, hKL, hnest, hcap, hL₀⟩ := exists_nested_full_compact_neighbourhoods_within
    K (targetDisc 0) hK hfull isOpen_ball hnorm
  have hfront (n : ℕ) : IsCompact (frontier (L n)) :=
    (hL n).1.of_isClosed_subset isClosed_frontier
      (frontier_subset_iff_isClosed.mpr (hL n).1.isClosed)
  have hnet (n : ℕ) := exists_finite_net (frontier (L n)) (hfront n)
    ((1 / 2 : ℝ) ^ n) (by positivity)
  choose P hPf hPL hPnet using hnet
  let D : UniformEscapeData := {
    K := L
    compact := fun n => (hL n).1
    full := fun n => (hL n).2
    nested := hnest
    normalized := hL₀
    P := P
    compactP := fun n => (hPf n).isCompact
    fullP := fun n => by
      simpa only [empty_union] using isConnected_compl_union_finite ∅ (P n)
        isCompact_empty (by simpa only [compl_empty] using (isConnected_univ : IsConnected (univ : Set ℂ)))
        (hPf n)
    boundary := hPL
  }
  have hsubset (n : ℕ) : K ⊆ L n := (hKL n).trans interior_subset
  refine ⟨D, hsubset, hcap, ?_⟩
  exact frontier_subset_closure_union_nets K hK.isClosed L P
    (fun n => (hL n).1.isClosed) D.antitone hsubset hcap _
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) hPnet

end EremenkosConjecture
