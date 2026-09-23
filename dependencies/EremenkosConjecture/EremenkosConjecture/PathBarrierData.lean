import EremenkosConjecture.NestedJordanNeighbourhoods
import EremenkosConjecture.BoundaryApproximation
import EremenkosConjecture.PathBarriers
import EremenkosConjecture.ConstructionData
import EremenkosConjecture.FullUnions

open Set Metric Filter Function
open scoped Topology

namespace EremenkosConjecture

structure PathBarrierData (X : Set ℂ) where
  data : UniformEscapeData
  contains : ∀ n, X ⊆ data.K n
  intersection : (⋂ n, data.K n) = X
  accumulation : frontier X ⊆ closure (⋃ n, data.P n)
  nonempty : ∀ n, (data.P n).Nonempty
  barrier : ∀ g : ℝ → ℂ, Continuous g → g 0 ∈ X → g 1 ∉ X →
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ n, g t ∉ data.P n) → False

theorem exists_pathBarrierData (K : Set ℂ) (hK : IsCompact K)
    (hconn : IsConnected K) (hfull : IsConnected Kᶜ) (hnorm : K ⊆ targetDisc 0)
    {a b : ℂ} (ha : a ∈ frontier K) (hb : b ∈ frontier K) (hab : a ≠ b) :
    Nonempty (PathBarrierData K) := by
  classical
  obtain ⟨J, hnest, hcap, hJ₀⟩ := exists_nested_jordan_neighbourhoods_within K (targetDisc 0)
    hK hconn hfull isOpen_ball hnorm
  let L : ℕ → Set ℂ := fun n => (J n).carrier
  have hLanti : Antitone L := antitone_nat_of_succ_le
    (fun n => (hnest n).trans interior_subset)
  have hKL (n : ℕ) : K ⊆ L n := (J n).contains.trans interior_subset
  have hproper (n : ℕ) : L n ≠ univ := by
    intro H
    have hn := (J n).full.nonempty
    change ((L n)ᶜ).Nonempty at hn
    simpa [H] using hn
  obtain ⟨c₀, hc₀, ht₀⟩ := exists_boundary_approximating_sequence hK.isClosed L
    (fun n => (J n).compact) hLanti hKL hcap hproper ha
  obtain ⟨c₁, hc₁, ht₁⟩ := exists_boundary_approximating_sequence hK.isClosed L
    (fun n => (J n).compact) hLanti hKL hcap hproper hb
  let c : ℕ → ℂ := fun n => if n % 2 = 0 then c₀ n else c₁ n
  have hc (n : ℕ) : c n ∈ frontier (L n) := by
    dsimp [c]
    split_ifs <;> [exact hc₀ n; exact hc₁ n]
  let ρ : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n
  have hρ (n : ℕ) : 0 < ρ n := by dsimp [ρ]; positivity
  have htρ : Tendsto ρ atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hfront (n : ℕ) : IsCompact (frontier (L n)) :=
    (J n).compact.of_isClosed_subset isClosed_frontier
      (frontier_subset_iff_isClosed.mpr (J n).compact.isClosed)
  choose Q hQf hQL hQnet using (fun n => exists_finite_net (frontier (L n)) (hfront n) (ρ n) (hρ n))
  let P : ℕ → Set ℂ := fun n => (frontier (L n) \ ball (c n) (ρ n)) ∪ Q n
  have hF (n : ℕ) := boundary_sdiff_ball_isCompact_isFull (J n).compact
    (J n).connectedInterior (J n).full (J n).regular (hc n) (hρ n)
  let D : UniformEscapeData := {
    K := L
    compact := fun n => (J n).compact
    full := fun n => (J n).full
    nested := hnest
    normalized := hJ₀
    P := P
    compactP := fun n => (hF n).1.union (hQf n).isCompact
    fullP := fun n => isConnected_compl_union_finite _ _ (hF n).1 (hF n).2 (hQf n)
    boundary := fun n => union_subset sdiff_subset (hQL n)
  }
  have hPnet : ∀ n, ∀ q ∈ frontier (L n), ∃ p ∈ P n, dist q p < ρ n := by
    intro n q hq
    obtain ⟨p, hp, hqp⟩ := hQnet n q hq
    exact ⟨p, Or.inr hp, hqp⟩
  have hacc := frontier_subset_closure_union_nets K hK.isClosed L P
    (fun n => (J n).compact.isClosed) hLanti hKL hcap ρ htρ hPnet
  let ε : ℕ → ℝ := fun n => dist (c₀ n) a + dist (c₁ n) b + ρ n
  have htε : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, dist_self, zero_add] using
      ((ht₀.dist (show Tendsto (fun _ : ℕ => a) atTop (𝓝 a) from tendsto_const_nhds)).add
        (ht₁.dist (show Tendsto (fun _ : ℕ => b) atTop (𝓝 b) from tendsto_const_nhds))).add htρ
  have hgate (n : ℕ) (z : ℂ) (hz : z ∈ frontier (L n)) (hzP : z ∉ P n) :
      dist z (c n) < ρ n := by
    by_contra H
    exact hzP (Or.inl ⟨hz, H⟩)
  refine ⟨{
    data := D
    contains := hKL
    intersection := hcap
    accumulation := hacc
    nonempty := fun n => by
      obtain ⟨p, hp, _⟩ := hPnet n (c₀ n) (hc₀ n)
      exact ⟨p, hp⟩
    barrier := ?_
  }⟩
  intro g hg hstart hend havoid
  apply no_curve_through_alternating_openings K L P (fun n => (J n).compact.isClosed)
    hLanti hKL hcap a b hab ε htε ?_ ?_ hg hstart hend havoid
  · intro n z hz hzP
    have H := hgate (2 * n) z hz hzP
    have heq : c (2 * n) = c₀ (2 * n) := by simp [c]
    rw [heq] at H
    have htri := dist_triangle z (c₀ (2 * n)) a
    dsimp [ε]
    linarith [show 0 ≤ dist (c₁ (2 * n)) b from dist_nonneg]
  · intro n z hz hzP
    have H := hgate (2 * n + 1) z hz hzP
    have heq : c (2 * n + 1) = c₁ (2 * n + 1) := by simp [c]
    rw [heq] at H
    have htri := dist_triangle z (c₁ (2 * n + 1)) b
    dsimp [ε]
    linarith [show 0 ≤ dist (c₀ (2 * n + 1)) a from dist_nonneg]

end EremenkosConjecture
