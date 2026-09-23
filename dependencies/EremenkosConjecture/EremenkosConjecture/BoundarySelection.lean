import EremenkosConjecture.FullNeighbourhoods
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Finite boundary nets accumulating on a compact set's boundary -/

open Set Metric Filter
open scoped Topology

namespace EremenkosConjecture

theorem exists_finite_net (A : Set ℂ) (hA : IsCompact A) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : Set ℂ, P.Finite ∧ P ⊆ A ∧ ∀ z ∈ A, ∃ p ∈ P, dist z p < ε := by
  classical
  have hcover : A ⊆ ⋃ a : A, ball (a : ℂ) ε := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self hε⟩
  obtain ⟨s, hs⟩ := hA.elim_finite_subcover (fun a : A => ball (a : ℂ) ε)
    (fun _ => isOpen_ball) hcover
  refine ⟨Subtype.val '' (s : Set A), s.finite_toSet.image _, ?_, ?_⟩
  · rintro z ⟨a, ha, rfl⟩
    exact a.property
  · intro z hz
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp (hs hz)
    exact ⟨a, mem_image_of_mem _ ha, hza⟩

theorem exists_frontier_near_of_mem_of_not_mem (A : Set ℂ) (hA : IsClosed A)
    {z w : ℂ} (hz : z ∈ A) (hw : w ∉ A) {ε : ℝ} (hε : 0 < ε) (hzw : dist z w < ε) :
    ∃ q ∈ frontier A, dist z q < ε := by
  by_contra! hnone
  have hcover : ball z ε ⊆ interior A ∪ Aᶜ := by
    intro q hq
    by_cases hqA : q ∈ A
    · left
      by_contra hqi
      have hqfront : q ∈ frontier A := ⟨hA.closure_eq.symm ▸ hqA, hqi⟩
      have H := hnone q hqfront
      have hq' : dist z q < ε := by simpa only [mem_ball, dist_comm] using hq
      exact (not_lt_of_ge H) hq'
    · exact Or.inr hqA
  have hd : Disjoint (interior A) Aᶜ := Set.disjoint_left.mpr
    (fun _ h₁ h₂ => h₂ (interior_subset h₁))
  rcases (convex_ball z ε : Convex ℝ (ball z ε)).isPreconnected.subset_or_subset isOpen_interior
      hA.isOpen_compl hd hcover with hleft | hright
  · exact hw (interior_subset (hleft (by simpa only [mem_ball, dist_comm] using hzw)))
  · exact hright (mem_ball_self hε) hz

theorem frontier_subset_closure_union_nets (K : Set ℂ) (hK : IsClosed K)
    (L P : ℕ → Set ℂ) (hL : ∀ n, IsClosed (L n)) (hanti : Antitone L)
    (hKL : ∀ n, K ⊆ L n) (hcap : (⋂ n, L n) = K)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hnet : ∀ n, ∀ q ∈ frontier (L n), ∃ p ∈ P n, dist q p < ε n) :
    frontier K ⊆ closure (⋃ n, P n) := by
  intro z hz
  have hzK : z ∈ K := hK.closure_eq ▸ hz.1
  have hzcompl : z ∈ closure Kᶜ := by
    rw [frontier_eq_closure_inter_closure] at hz
    exact hz.2
  rw [Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨w, hw, hzw⟩ := Metric.mem_closure_iff.mp hzcompl (δ / 2) (half_pos hδ)
  have hex : ∃ N, w ∉ L N := by
    by_contra! H
    exact hw (hcap ▸ mem_iInter.mpr H)
  obtain ⟨N₁, hN₁⟩ := hex
  have hevent : ∀ᶠ n : ℕ in atTop, ε n < δ / 2 :=
    hε.eventually (Iio_mem_nhds (half_pos hδ))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hevent
  let n := max N₁ N₂
  have hwn : w ∉ L n := fun h => hN₁ (hanti (le_max_left _ _) h)
  obtain ⟨q, hq, hzq⟩ := exists_frontier_near_of_mem_of_not_mem (L n) (hL n)
    (hKL n hzK) hwn (half_pos hδ) hzw
  obtain ⟨p, hp, hqp⟩ := hnet n q hq
  refine ⟨p, mem_iUnion.mpr ⟨n, hp⟩, ?_⟩
  have heps := hN₂ n (le_max_right _ _)
  exact (dist_triangle z q p).trans_lt (by linarith)

end EremenkosConjecture
