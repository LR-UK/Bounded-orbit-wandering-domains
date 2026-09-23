import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

open Set Filter Metric Bornology
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Any closed plane set with unbounded complement leaves room for disjoint
closed discs escaping to infinity with radii tending to zero. These are the
auxiliary return channels in oscillating realisation. -/
theorem exists_disjoint_escaping_discs {A : Set ℂ} (hA : IsClosed A)
    (hunbounded : ¬ IsBounded Aᶜ) :
    ∃ (c : ℕ → ℂ) (r : ℕ → ℝ),
      (∀ n, 0 < r n ∧ r n ≤ 1 / ((n : ℝ)+1)) ∧
      (∀ n, Disjoint (closedBall (c n) (r n)) A) ∧
      Pairwise (fun i j => Disjoint (closedBall (c i) (r i)) (closedBall (c j) (r j))) ∧
      Tendsto r atTop (𝓝 0) ∧
      ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ closedBall (c n) (r n), R < ‖z‖ := by
  classical
  have hex : ∀ R : ℝ, ∃ z ∈ Aᶜ, R < ‖z‖ := by
    intro R
    by_contra! h
    exact hunbounded (isBounded_iff_forall_norm_le.mpr ⟨R,h⟩)
  choose point hpA hpR using hex
  let c : ℕ → ℂ := Nat.rec (point 0) (fun _ z => point (‖z‖+4))
  have hcA : ∀ n, c n ∈ Aᶜ := by
    intro n
    cases n with
    | zero => exact hpA 0
    | succ n => exact hpA (‖c n‖+4)
  have hgap : ∀ n, ‖c n‖ + 4 < ‖c (n+1)‖ := fun n => hpR (‖c n‖+4)
  have hmono : StrictMono (fun n => ‖c n‖) :=
    strictMono_nat_of_lt_succ (fun n => by linarith [hgap n])
  have hlarge : ∀ n : ℕ, 4 * (n : ℝ) < ‖c n‖ := by
    intro n
    induction n with
    | zero => simpa [c] using hpR 0
    | succ n ih =>
      have H := hgap n
      push_cast
      linarith
  have hballs : ∀ n, ∃ s > 0, closedBall (c n) s ⊆ Aᶜ := fun n =>
    Metric.nhds_basis_closedBall.mem_iff.mp (hA.isOpen_compl.mem_nhds (hcA n))
  choose s hs hsub using hballs
  let r : ℕ → ℝ := fun n => min (s n) (1/((n : ℝ)+1))
  have hr : ∀ n, 0 < r n := fun n => lt_min (hs n) (by positivity)
  have hrle : ∀ n, r n ≤ 1/((n : ℝ)+1) := fun n => min_le_right _ _
  have hr1 : ∀ n, r n ≤ 1 := by
    intro n
    apply (hrle n).trans
    apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ)+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hpair : ∀ i j : ℕ, i < j →
      Disjoint (closedBall (c i) (r i)) (closedBall (c j) (r j)) := by
    intro i j hij
    apply closedBall_disjoint_closedBall
    have H := (hgap i).trans_le (hmono.monotone (Nat.succ_le_of_lt hij))
    have htri := norm_le_norm_sub_add (c j) (c i)
    rw [norm_sub_rev] at htri
    rw [dist_eq_norm]
    linarith [hr1 i, hr1 j]
  refine ⟨c,r,fun n => ⟨hr n,hrle n⟩,?_,?_,?_,?_⟩
  · intro n
    exact disjoint_left.mpr (fun z hz hza =>
      hsub n (closedBall_subset_closedBall (min_le_left _ _) hz) hza)
  · intro i j hij
    rcases hij.lt_or_gt with h | h
    · exact hpair i j h
    · exact (hpair j i h).symm
  · exact squeeze_zero (fun n => (hr n).le) hrle
      tendsto_one_div_add_atTop_nhds_zero_nat
  · intro R
    have hn : Tendsto (fun n : ℕ => 4 * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 4)
    filter_upwards [hn.eventually (eventually_gt_atTop (R+1))] with n hn z hz
    have hd0 : ‖z-c n‖ ≤ r n := by
      simpa only [mem_closedBall, dist_eq_norm] using hz
    have hd : ‖z-c n‖ ≤ 1 := hd0.trans (hr1 n)
    have ht := norm_le_norm_sub_add (c n) z
    rw [norm_sub_rev] at ht
    linarith [hlarge n]

end FunctionTheory
