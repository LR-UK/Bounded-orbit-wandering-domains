import EremenkosConjecture.BoundarySelection
import Mathlib.Topology.Order.Compact

open Set Metric Filter
open scoped Topology

namespace EremenkosConjecture

/-- Every point of the limiting boundary is approached by points on the
boundaries of all the nested compact neighbourhoods. -/
theorem exists_boundary_approximating_sequence
    {K : Set ℂ} (hK : IsClosed K) (L : ℕ → Set ℂ)
    (hL : ∀ n, IsCompact (L n)) (hanti : Antitone L)
    (hKL : ∀ n, K ⊆ L n) (hcap : (⋂ n, L n) = K)
    (hproper : ∀ n, L n ≠ univ) {a : ℂ} (ha : a ∈ frontier K) :
    ∃ c : ℕ → ℂ, (∀ n, c n ∈ frontier (L n)) ∧ Tendsto c atTop (𝓝 a) := by
  have haK : a ∈ K := hK.closure_eq ▸ ha.1
  have hfront (n : ℕ) : IsCompact (frontier (L n)) :=
    (hL n).of_isClosed_subset isClosed_frontier
      (frontier_subset_iff_isClosed.mpr (hL n).isClosed)
  have hfne (n : ℕ) : (frontier (L n)).Nonempty :=
    nonempty_frontier_iff.mpr ⟨⟨a, hKL n haK⟩, hproper n⟩
  have hmin (n : ℕ) := (hfront n).exists_isMinOn (f := fun z : ℂ => dist a z) (hfne n)
    (continuous_const.dist continuous_id).continuousOn
  choose c hc hcm using hmin
  refine ⟨c, hc, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  have hac : a ∈ closure Kᶜ := by
    rw [frontier_eq_closure_inter_closure] at ha
    exact ha.2
  obtain ⟨w, hw, haw⟩ := Metric.mem_closure_iff.mp hac ε hε
  have hex : ∃ N, w ∉ L N := by
    by_contra! H
    exact hw (hcap ▸ mem_iInter.mpr H)
  obtain ⟨N, hN⟩ := hex
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨q, hq, haq⟩ := exists_frontier_near_of_mem_of_not_mem (L n) (hL n).isClosed
    (hKL n haK) (fun H => hN (hanti hn H)) hε haw
  have H := hcm n hq
  simpa only [dist_comm] using H.trans_lt haq

end EremenkosConjecture
