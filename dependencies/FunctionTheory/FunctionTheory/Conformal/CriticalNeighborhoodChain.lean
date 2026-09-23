import FunctionTheory.Analytic.CriticalNeighborhood

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- A finite chain of compact holomorphic models admits nested working
neighbourhoods with compact closure, image containment, and no additional
critical points, including on their boundaries. This supplies the closure
hypotheses of finite conformal correction from compact-set data. -/
theorem exists_finite_critical_neighborhood_chain
    (N : ℕ) (K U C : ℕ → Set ℂ) (f : ℕ → ℂ → ℂ)
    (hK : ∀ n ≤ N, IsCompact (K n)) (hU : ∀ n ≤ N, IsOpen (U n))
    (hKU : ∀ n ≤ N, K n ⊆ U n)
    (hf : ∀ n ≤ N, AnalyticOnNhd ℂ (f n) (U n))
    (hnc : ∀ n ≤ N, ∀ a ∈ K n, ¬ ∀ᶠ z in 𝓝 a, f n z = f n a)
    (hcritical : ∀ n ≤ N, ∀ a ∈ K n, deriv (f n) a = 0 → a ∈ C n)
    (himage : ∀ n < N, MapsTo (f n) (K n) (K (n + 1))) :
    ∃ V : ℕ → Set ℂ,
      (∀ n ≤ N, IsOpen (V n) ∧ K n ⊆ V n ∧ closure (V n) ⊆ U n ∧
        IsCompact (closure (V n)) ∧
        ∀ z ∈ closure (V n), deriv (f n) z = 0 → z ∈ C n) ∧
      ∀ n < N, MapsTo (f n) (closure (V n)) (V (n + 1)) := by
  induction N generalizing K U C f with
  | zero =>
    obtain ⟨V, hV, hKV, hVU, hVc, hc⟩ := exists_critical_control_neighborhood
      (hK 0 le_rfl) (hU 0 le_rfl) (hKU 0 le_rfl) (hf 0 le_rfl)
      (hnc 0 le_rfl) (hcritical 0 le_rfl)
    refine ⟨fun _ => V, ?_, ?_⟩
    · intro n hn
      have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
      subst n
      exact ⟨hV, hKV, hVU, hVc, hc⟩
    · intro n hn
      exact (Nat.not_lt_zero n hn).elim
  | succ N ih =>
    obtain ⟨W, HW, Hmap⟩ := ih
      (K := fun n => K (n + 1)) (U := fun n => U (n + 1))
      (C := fun n => C (n + 1)) (f := fun n => f (n + 1))
      (fun n hn => hK (n + 1) (Nat.succ_le_succ hn))
      (fun n hn => hU (n + 1) (Nat.succ_le_succ hn))
      (fun n hn => hKU (n + 1) (Nat.succ_le_succ hn))
      (fun n hn => hf (n + 1) (Nat.succ_le_succ hn))
      (fun n hn => hnc (n + 1) (Nat.succ_le_succ hn))
      (fun n hn => hcritical (n + 1) (Nat.succ_le_succ hn))
      (fun n hn => himage (n + 1) (Nat.succ_lt_succ hn))
    let O := U 0 ∩ f 0 ⁻¹' W 0
    have hO : IsOpen O :=
      (hf 0 (Nat.zero_le _)).continuousOn.isOpen_inter_preimage
        (hU 0 (Nat.zero_le _)) (HW 0 (Nat.zero_le _)).1
    have hKO : K 0 ⊆ O := by
      intro z hz
      exact ⟨hKU 0 (Nat.zero_le _) hz,
        (HW 0 (Nat.zero_le _)).2.1 (himage 0 (Nat.zero_lt_succ N) hz)⟩
    obtain ⟨V₀, hV₀, hKV₀, hV₀O, hV₀c, hcrit₀⟩ :=
      exists_critical_control_neighborhood (hK 0 (Nat.zero_le _)) hO hKO
        ((hf 0 (Nat.zero_le _)).mono inter_subset_left)
        (hnc 0 (Nat.zero_le _)) (hcritical 0 (Nat.zero_le _))
    let V : ℕ → Set ℂ := fun n => Nat.casesOn n V₀ W
    refine ⟨V, ?_, ?_⟩
    · intro n hn
      cases n with
      | zero =>
        exact ⟨hV₀, hKV₀, fun z hz => (hV₀O hz).1, hV₀c, hcrit₀⟩
      | succ n =>
        exact HW n (Nat.le_of_succ_le_succ hn)
    · intro n hn
      cases n with
      | zero =>
        exact fun z hz => (hV₀O hz).2
      | succ n =>
        exact Hmap n (Nat.lt_of_succ_lt_succ hn)

end FunctionTheory
