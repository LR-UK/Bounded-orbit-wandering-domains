import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- An exhaustion that contains earlier compact pieces and excludes later
pieces by removing their prescribed open outer neighbourhoods. -/
def separatedExhaustion {E : Type*} [NormedAddCommGroup E]
    (A Z : ℕ → Set E) (B : Set E) (n : ℕ) : Set E :=
  ((closedBall 0 (n : ℝ) ∪ ⋃ i : Fin n, A i) ∪ B) \ ⋃ j, ⋃ (_ : n ≤ j), Z j

theorem isCompact_separatedExhaustion
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (A Z : ℕ → Set E) (B : Set E)
    (hA : ∀ n, IsCompact (A n)) (hZ : ∀ n, IsOpen (Z n)) (hB : IsCompact B)
    (n : ℕ) : IsCompact (separatedExhaustion A Z B n) := by
  exact ((isCompact_closedBall (0 : E) n).union (isCompact_iUnion (fun i : Fin n => hA i))).union hB
    |>.diff (isOpen_iUnion (fun j => isOpen_iUnion (fun _ => hZ j)))

theorem monotone_separatedExhaustion
    {E : Type*} [NormedAddCommGroup E] (A Z : ℕ → Set E) (B : Set E) :
    Monotone (separatedExhaustion A Z B) := by
  intro n m hnm z hz
  refine ⟨?_, ?_⟩
  · rcases hz.1 with (hb | hA) | hB
    · exact Or.inl (Or.inl (closedBall_subset_closedBall (Nat.cast_le.mpr hnm) hb))
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hA
      exact Or.inl (Or.inr (mem_iUnion.mpr ⟨⟨i, i.isLt.trans_le hnm⟩, hi⟩))
    · exact Or.inr hB
  · intro H
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp H
    exact hz.2 (mem_iUnion₂.mpr ⟨j, hnm.trans hj, hzj⟩)

theorem subset_separatedExhaustion_of_disjoint
    {E : Type*} [NormedAddCommGroup E] (A Z : ℕ → Set E) (B : Set E)
    (hB : Disjoint B (⋃ j, Z j)) (n : ℕ) :
    B ⊆ separatedExhaustion A Z B n := by
  intro z hz
  refine ⟨Or.inr hz, ?_⟩
  intro H
  obtain ⟨j, _, hzj⟩ := mem_iUnion₂.mp H
  exact Set.disjoint_left.mp hB hz (mem_iUnion.mpr ⟨j, hzj⟩)

theorem earlier_subset_separatedExhaustion
    {E : Type*} [NormedAddCommGroup E] (A Z : ℕ → Set E) (B : Set E)
    (hAZ : ∀ j, A j ⊆ Z j) (hdis : Pairwise (fun i j => Disjoint (Z i) (Z j)))
    {m n : ℕ} (hm : m < n) : A m ⊆ separatedExhaustion A Z B n := by
  intro z hz
  refine ⟨Or.inl (Or.inr (mem_iUnion.mpr ⟨⟨m, hm⟩, hz⟩)), ?_⟩
  intro H
  obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp H
  exact Set.disjoint_left.mp (hdis (show m ≠ j by omega)) (hAZ m hz) hzj

theorem disjoint_separatedExhaustion_later
    {E : Type*} [NormedAddCommGroup E] (A Z : ℕ → Set E) (B : Set E)
    (hAZ : ∀ j, A j ⊆ Z j) {n j : ℕ} (hj : n ≤ j) :
    Disjoint (separatedExhaustion A Z B n) (A j) := by
  apply Set.disjoint_left.mpr
  intro z hz hza
  exact hz.2 (mem_iUnion₂.mpr ⟨j, hj, hAZ j hza⟩)

/-- The exhaustion is cofinal on compact subsets of the plane, with
containment in interiors. Merely covering the plane by compact sets would
not suffice for the later meromorphic-limit argument. -/
theorem compact_eventually_subset_interior_separatedExhaustion
    {E : Type*} [NormedAddCommGroup E]
    (A Z : ℕ → Set E) (B : Set E)
    (hescape : ∀ R : ℝ, ∀ᶠ j in atTop, ∀ z ∈ Z j, R < ‖z‖)
    {P : Set E} (hP : IsCompact P) :
    ∃ N : ℕ, ∀ n ≥ N, P ⊆ interior (separatedExhaustion A Z B n) := by
  have hcover : ∀ x : E, ∃ n, x ∈ interior (separatedExhaustion A Z B n) := by
    intro x
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hescape (‖x‖ + 2))
    obtain ⟨L, hL⟩ := exists_nat_gt (‖x‖ + 1)
    let n := max N L
    have hball : ball x 1 ⊆ separatedExhaustion A Z B n := by
      intro z hz
      have hd : ‖z - x‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hz
      have hnorm : ‖z‖ < ‖x‖ + 1 := by
        have H := norm_le_norm_sub_add z x
        linarith
      refine ⟨Or.inl (Or.inl ?_), ?_⟩
      · rw [mem_closedBall, dist_zero_right]
        exact hnorm.le.trans (hL.le.trans (Nat.cast_le.mpr (le_max_right N L)))
      · intro H
        obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp H
        have Hj := hN j ((le_max_left N L).trans hj) z hzj
        linarith
    exact ⟨n, mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (ball_mem_nhds x (by norm_num)) hball)⟩
  have hdirected : Directed (· ⊆ ·) (fun n => interior (separatedExhaustion A Z B n)) := by
    intro n m
    exact ⟨max n m, interior_mono (monotone_separatedExhaustion A Z B (le_max_left _ _)),
      interior_mono (monotone_separatedExhaustion A Z B (le_max_right _ _))⟩
  obtain ⟨N, hN⟩ := hP.elim_directed_cover
    (fun n => interior (separatedExhaustion A Z B n)) (fun _ => isOpen_interior)
    (fun x _ => mem_iUnion.mpr (hcover x)) hdirected
  exact ⟨N, fun n hn => hN.trans
    (interior_mono (monotone_separatedExhaustion A Z B hn))⟩

end FunctionTheory
