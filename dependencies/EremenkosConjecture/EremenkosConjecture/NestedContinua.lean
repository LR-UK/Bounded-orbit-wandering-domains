import EremenkosConjecture.PlaneTopology
import Mathlib.Topology.Separation.Hausdorff

open Set

namespace EremenkosConjecture

theorem exists_stage_subset_open {K : ℕ → Set ℂ} (hK : ∀ n, IsCompact (K n))
    (hanti : Antitone K) {U : Set ℂ} (hU : IsOpen U) (hKU : (⋂ n, K n) ⊆ U) :
    ∃ n, K n ⊆ U := by
  by_contra! H
  have hne (n : ℕ) : (K n \ U).Nonempty := by
    obtain ⟨x, hx, hxU⟩ := not_subset.mp (H n)
    exact ⟨x, hx, hxU⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => K n \ U) (fun n => sdiff_subset_sdiff_left (hanti (Nat.le_succ n))) hne
    ((hK 0).diff hU) (fun n => ((hK n).diff hU).isClosed)
  have hxK : x ∈ ⋂ n, K n := mem_iInter.mpr (fun n => (mem_iInter.mp hx n).1)
  exact (mem_iInter.mp hx 0).2 (hKU hxK)

/-- The decreasing intersection of nonempty compact connected plane sets is connected. -/
theorem isConnected_nested_inter {K : ℕ → Set ℂ} (hK : ∀ n, IsCompact (K n))
    (hconn : ∀ n, IsConnected (K n)) (hanti : Antitone K) : IsConnected (⋂ n, K n) := by
  have hcompact : IsCompact (⋂ n, K n) := (hK 0).of_isClosed_subset
    (isClosed_iInter (fun n => (hK n).isClosed)) (iInter_subset K 0)
  refine ⟨IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K
    (fun n => hanti (Nat.le_succ n)) (fun n => (hconn n).nonempty) (hK 0)
    (fun n => (hK n).isClosed), ?_⟩
  apply isPreconnected_closed_iff.mpr
  intro A B hA hB hcover hSA hSB
  by_contra H
  have hdis : Disjoint ((⋂ n, K n) ∩ A) ((⋂ n, K n) ∩ B) := by
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    exact H ⟨x, hxA.1, hxA.2, hxB.2⟩
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hcompact.inter_right hA) (hcompact.inter_right hB) hdis
  have hsub : (⋂ n, K n) ⊆ U ∪ V := by
    intro x hx
    rcases hcover hx with hxA | hxB
    · exact Or.inl (hAU ⟨hx, hxA⟩)
    · exact Or.inr (hBV ⟨hx, hxB⟩)
  obtain ⟨n, hn⟩ := exists_stage_subset_open hK hanti (hU.union hV) hsub
  obtain ⟨a, haK, haA⟩ := hSA
  obtain ⟨b, hbK, hbB⟩ := hSB
  obtain ⟨x, _, hxU, hxV⟩ := (hconn n).isPreconnected U V hU hV hn
    ⟨a, mem_iInter.mp haK n, hAU ⟨haK, haA⟩⟩
    ⟨b, mem_iInter.mp hbK n, hBV ⟨hbK, hbB⟩⟩
  exact Set.disjoint_left.mp hUV hxU hxV

end EremenkosConjecture
