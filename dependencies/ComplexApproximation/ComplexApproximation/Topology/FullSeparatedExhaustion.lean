import ComplexApproximation.Topology.FullFamilyFilling
import FunctionTheory.Topology.LocallyFiniteCompactFamily
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Data.Nat.Find

open Set Filter Metric Bornology Polynomial
open scoped Topology

namespace ComplexApproximation

set_option autoImplicit false

private theorem full_closedBall (c : ℂ) (r : ℝ) :
    IsConnected (closedBall c r)ᶜ := by
  apply isConnected_compl_of_polynomial_separation _ (isCompact_closedBall c r)
  intro z hz
  refine ⟨X - C c, r, ?_, ?_⟩
  · intro w hw
    simpa only [eval_sub, eval_X, eval_C, mem_closedBall, dist_eq_norm] using hw
  · simpa only [eval_sub, eval_X, eval_C, mem_closedBall, dist_eq_norm, not_le] using hz

/-- A disjoint escaping full compact family admits an increasing full compact
exhaustion separating earlier members from later ones, and retaining a fixed
disjoint trapping disc. Cofinality holds in interiors. -/
theorem exists_full_separating_exhaustion
    (K : ℕ → Set ℂ) (hK : ∀ n, IsCompact (K n))
    (hfull : ∀ n, IsConnected (K n)ᶜ)
    (hdis : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hescape : ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K n, R < ‖z‖)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hD : Disjoint (closedBall c ρ) (⋃ n, K n)) :
    ∃ A : ℕ → Set ℂ,
      (∀ n, IsCompact (A n)) ∧
      (∀ n, IsConnected (A n)ᶜ) ∧ Monotone A ∧
      (∀ m n, m < n → K m ⊆ A n) ∧
      (∀ n j, n ≤ j → Disjoint (A n) (K j)) ∧
      (∀ n, closedBall c ρ ⊆ A n) ∧
      ∀ P : Set ℂ, IsCompact P → ∃ N, ∀ n ≥ N, P ⊆ interior (A n) := by
  classical
  let B : ℕ → Set ℂ := fun r => closedBall c (ρ + r)
  have hBc : ∀ r, IsCompact (B r) := fun r => isCompact_closedBall c (ρ + r)
  have hBmono : Monotone B := by
    intro r s hrs
    apply closedBall_subset_closedBall
    have hcast : (r : ℝ) ≤ s := Nat.cast_le.mpr hrs
    linarith
  have hloc := FunctionTheory.locallyFinite_of_uniform_norm_escape K hescape
  let S : ℕ → Finset ℕ := fun r => (hloc.finite_nonempty_inter_compact (hBc r)).toFinset
  have hS : ∀ r i, i ∈ S r ↔ (K i ∩ B r).Nonempty := by
    intro r i
    exact (hloc.finite_nonempty_inter_compact (hBc r)).mem_toFinset
  let H : ℕ → Set ℂ := fun r => fill (B r ∪ ⋃ i ∈ S r, K i)
  have hHc : ∀ r, IsCompact (H r) := fun r =>
    isCompact_fill ((hBc r).union ((S r).isCompact_biUnion (fun i _ => hK i)))
  have hBH : ∀ r, B r ⊆ H r := fun r =>
    subset_union_left.trans (subset_fill _)
  have hS0 : S 0 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨z, hzK, hzB⟩ := (hS 0 i).mp hi
    have hzD : z ∈ closedBall c ρ := by simpa [B] using hzB
    exact disjoint_left.mp hD hzD (mem_iUnion.mpr ⟨i, hzK⟩)
  have hH0 : H 0 = closedBall c ρ := by
    simpa [H, hS0, B] using
      fill_eq_self_of_full_compact (isCompact_closedBall c ρ) (full_closedBall c ρ)
  have hthreshold : ∀ r, ∃ N : ℕ, ∀ j ≥ N, Disjoint (H r) (K j) := by
    intro r
    obtain ⟨R, _, hR⟩ := (hHc r).isBounded.exists_pos_norm_le
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hescape R)
    refine ⟨N, fun j hj => disjoint_left.mpr ?_⟩
    intro z hzH hzK
    exact (not_lt_of_ge (hR z hzH)) (hN j hj z hzK)
  choose N₀ hN₀ using hthreshold
  let N : ℕ → ℕ := fun r => if r = 0 then 0 else N₀ r
  have hN : ∀ r j, N r ≤ j → Disjoint (H r) (K j) := by
    intro r j hj
    by_cases hr : r = 0
    · subst r
      rw [hH0]
      exact hD.mono_right (subset_iUnion K j)
    · exact hN₀ r j (by simpa only [N, if_neg hr] using hj)
  let r : ℕ → ℕ := fun n => Nat.findGreatest (fun k => N k ≤ n) n
  have hrvalid : ∀ n, N (r n) ≤ n := by
    intro n
    exact Nat.findGreatest_spec (P := fun k => N k ≤ n) (m := 0) (Nat.zero_le n) (by simp [N])
  have hrmono : Monotone r := by
    intro n m hnm
    exact Nat.findGreatest_mono (fun k hk => hk.trans hnm) hnm
  have hreventual : ∀ R : ℕ, ∀ n ≥ max R (N R), R ≤ r n := by
    intro R n hn
    exact Nat.le_findGreatest ((le_max_left _ _).trans hn) ((le_max_right _ _).trans hn)
  let A : ℕ → Set ℂ := fun n => fill (B (r n) ∪ ⋃ i ∈ Finset.range n, K i)
  have hbasec : ∀ n, IsCompact (B (r n) ∪ ⋃ i ∈ Finset.range n, K i) :=
    fun n => (hBc _).union ((Finset.range n).isCompact_biUnion (fun i _ => hK i))
  have hBA : ∀ n, B (r n) ⊆ A n := fun n =>
    subset_union_left.trans (subset_fill _)
  refine ⟨A, fun n => isCompact_fill (hbasec n),
    fun n => isConnected_compl_fill (hbasec n), ?_, ?_, ?_, ?_, ?_⟩
  · intro n m hnm
    apply fill_mono
    apply union_subset_union (hBmono (hrmono hnm))
    intro z hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hnm), hzi⟩
  · intro m n hmn z hz
    exact subset_fill _ (Or.inr (mem_iUnion₂.mpr ⟨m, Finset.mem_range.mpr hmn, hz⟩))
  · intro n j hnj
    have hST : S (r n) ⊆ Finset.range n := by
      intro i hi
      apply Finset.mem_range.mpr
      by_contra hin
      obtain ⟨z, hzK, hzB⟩ := (hS (r n) i).mp hi
      exact disjoint_left.mp (hN (r n) i ((hrvalid n).trans (by omega)))
        (hBH (r n) hzB) hzK
    have hfar : ∀ i ∈ Finset.range n \ S (r n), Disjoint (B (r n)) (K i) := by
      intro i hi
      apply disjoint_left.mpr
      intro z hzB hzK
      exact (Finset.mem_sdiff.mp hi).2 ((hS (r n) i).mpr ⟨z, hzK, hzB⟩)
    have heq := fill_union_finite_disjoint_full_family K hK hfull hdis
      (B (r n)) (hBc (r n)) (S (r n)) (Finset.range n) hST hfar
    change Disjoint (fill (B (r n) ∪ ⋃ i ∈ Finset.range n, K i)) (K j)
    rw [heq]
    apply disjoint_union_left.mpr
    refine ⟨hN (r n) j ((hrvalid n).trans hnj), ?_⟩
    apply disjoint_left.mpr
    intro z hz hzj
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz
    have hin := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
    exact disjoint_left.mp (hdis (show i ≠ j by omega)) hzi hzj
  · intro n
    have hD0 : closedBall c ρ = B 0 := by simp [B]
    rw [hD0]
    exact (hBmono (Nat.zero_le _)).trans (hBA n)
  · intro P hP
    obtain ⟨M, _, hM⟩ := hP.isBounded.exists_pos_norm_le
    obtain ⟨R, hR⟩ := exists_nat_gt (M + ‖c‖)
    refine ⟨max R (N R), fun n hn => ?_⟩
    have hball : ball c (ρ + r n) ⊆ interior (A n) :=
      isOpen_ball.subset_interior_iff.mpr (ball_subset_closedBall.trans (hBA n))
    intro z hz
    apply hball
    rw [mem_ball, dist_eq_norm]
    have hnorm := norm_sub_le z c
    have hMR := hM z hz
    have hRn : (R : ℝ) ≤ r n := by exact_mod_cast hreventual R n hn
    linarith

end ComplexApproximation
