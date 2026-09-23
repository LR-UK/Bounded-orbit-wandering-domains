import EremenkosConjecture.UniformIterateControl

/-! # Stability of unbounded iterates with quantitative ambient charts -/

open Set Metric Function
open scoped NNReal

namespace EremenkosConjecture

theorem approximate_bilipschitz_iterate
    (g : ℂ → ℂ) (E U A : Set ℂ) (hU : IsOpen U) (n : ℕ)
    (hcontrol : ∀ k < n, UniformControlOn g E ((g^[k]) '' U))
    (hgn : DifferentiableOn ℂ (g^[n]) U)
    (H : ℂ ≃ₜ ℂ) (heq : EqOn (g^[n]) H U) {L L' : ℝ≥0}
    (hL : LipschitzWith L H) (hL' : LipschitzWith L' H.symm)
    {r : ℝ} (hr : 0 < r) (htube : ∀ z ∈ A, ball z r ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℂ → ℂ, Differentiable ℂ f →
      (∀ z ∈ E, dist (f z) (g z) < δ) →
      (∃ G : ℂ ≃ₜ ℂ, EqOn (f^[n]) G A ∧ ∃ M M' : ℝ≥0,
        LipschitzWith M G ∧ LipschitzWith M' G.symm) ∧
      (∀ k ≤ n, ∀ z ∈ U, dist ((f^[k]) z) ((g^[k]) z) < ε) ∧
      (∀ k < n, MapsTo (f^[k]) U E) := by
  obtain ⟨η, hη, Hη⟩ := exists_bilipschitz_approximation_tolerance_of_extension
    hU hgn H heq hL hL' hr htube
  obtain ⟨δ, hδ, Hδ⟩ := iterate_approximation_of_uniform_control g E U n hcontrol
    (min ε η) (lt_min hε hη)
  refine ⟨δ, hδ, fun f hf hclose => ?_⟩
  obtain ⟨happrox, hdomain⟩ := Hδ f hclose
  refine ⟨Hη (f^[n]) (hf.iterate n).differentiableOn ?_, ?_, hdomain⟩
  · intro z hz
    exact ((happrox n le_rfl z hz).trans_le (min_le_right _ _)).le
  · intro k hk z hz
    exact (happrox k hk z hz).trans_le (min_le_left _ _)

private theorem exists_pos_le_finite_family {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) : ∃ r : ℝ, 0 < r ∧ ∀ i, r ≤ d i := by
  classical
  have hfinite (s : Finset ι) : ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, r ≤ d i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i s hi ih =>
        obtain ⟨r, hr, hbound⟩ := ih
        refine ⟨min r (d i), lt_min hr (hd i), ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hbound j hj)
  obtain ⟨r, hr, hbound⟩ := hfinite Finset.univ
  exact ⟨r, hr, fun i => hbound i (Finset.mem_univ i)⟩

theorem approximate_bilipschitz_iterates
    (g : ℂ → ℂ) (E U A : Set ℂ) (hU : IsOpen U) (n : ℕ)
    (hcontrol : ∀ k < n, UniformControlOn g E ((g^[k]) '' U))
    (hgn : ∀ k ≤ n, DifferentiableOn ℂ (g^[k]) U)
    (H : ℕ → ℂ ≃ₜ ℂ) (heq : ∀ k ≤ n, EqOn (g^[k]) (H k) U)
    (L L' : ℕ → ℝ≥0)
    (hL : ∀ k ≤ n, LipschitzWith (L k) (H k))
    (hL' : ∀ k ≤ n, LipschitzWith (L' k) (H k).symm)
    {r : ℝ} (hr : 0 < r) (htube : ∀ z ∈ A, ball z r ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℂ → ℂ, Differentiable ℂ f →
      (∀ z ∈ E, dist (f z) (g z) < δ) →
      (∀ k ≤ n, ∃ G : ℂ ≃ₜ ℂ, EqOn (f^[k]) G A ∧ ∃ M M' : ℝ≥0,
        LipschitzWith M G ∧ LipschitzWith M' G.symm) ∧
      (∀ k ≤ n, ∀ z ∈ U, dist ((f^[k]) z) ((g^[k]) z) < ε) ∧
      (∀ k < n, MapsTo (f^[k]) U E) := by
  classical
  have hcert (i : Fin (n + 1)) := approximate_bilipschitz_iterate g E U A hU i
    (fun k hk => hcontrol k (hk.trans_le (Nat.le_of_lt_succ i.isLt)))
    (hgn i (Nat.le_of_lt_succ i.isLt)) (H i) (heq i (Nat.le_of_lt_succ i.isLt))
    (hL i (Nat.le_of_lt_succ i.isLt)) (hL' i (Nat.le_of_lt_succ i.isLt)) hr htube hε
  choose d hd hcert using hcert
  obtain ⟨δ, hδ, hδd⟩ := exists_pos_le_finite_family d hd
  refine ⟨δ, hδ, fun f hf hclose => ?_⟩
  have hclose' (i : Fin (n + 1)) : ∀ z ∈ E, dist (f z) (g z) < d i :=
    fun z hz => (hclose z hz).trans_le (hδd i)
  have hlast := hcert ⟨n, Nat.lt_succ_self n⟩ f hf (hclose' _)
  refine ⟨?_, hlast.2⟩
  intro k hk
  exact (hcert ⟨k, Nat.lt_succ_of_le hk⟩ f hf (hclose' _)).1

end EremenkosConjecture
