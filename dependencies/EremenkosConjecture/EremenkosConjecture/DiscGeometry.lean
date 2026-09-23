import EremenkosConjecture.FullUnions
import ComplexDynamics.UniformEscape

/-! # The disks used in the uniform-escape construction -/

open Set Metric Polynomial Filter
open scoped Topology

namespace EremenkosConjecture

def targetDisc (n : ℕ) : Set ℂ := ball ((3 * n : ℝ) : ℂ) 1
def trappingDisc : Set ℂ := ball (-3) 1
def controlDisc (n : ℕ) : Set ℂ := closedBall (-3) (1 + 3 * n)

theorem isConnected_compl_closedBall (c : ℂ) (r : ℝ) :
    IsConnected (closedBall c r)ᶜ := by
  apply isConnected_compl_of_polynomial_separation _ (isCompact_closedBall _ _)
  intro z hz
  refine ⟨X - C c, r, ?_, ?_⟩
  · intro w hw
    simpa only [eval_sub, eval_X, eval_C, mem_closedBall, dist_eq_norm] using hw
  · simpa only [eval_sub, eval_X, eval_C, mem_closedBall, dist_eq_norm, not_le] using hz

theorem targetDisc_re_bounds {n : ℕ} {z : ℂ} (hz : z ∈ targetDisc n) :
    3 * n - 1 < z.re ∧ z.re < 3 * n + 1 := by
  have hnorm : ‖z - ((3 * n : ℝ) : ℂ)‖ < 1 := by
    simpa only [targetDisc, mem_ball, dist_eq_norm] using hz
  have h := (Complex.abs_re_le_norm (z - ((3 * n : ℝ) : ℂ))).trans_lt hnorm
  simp only [Complex.sub_re, Complex.ofReal_re] at h
  obtain ⟨h₁, h₂⟩ := abs_lt.mp h
  constructor <;> linarith

theorem disjoint_targetDisc {n m : ℕ} (hnm : n ≠ m) :
    Disjoint (targetDisc n) (targetDisc m) := by
  apply Set.disjoint_left.mpr
  intro z hzn hzm
  obtain ⟨hn₁, hn₂⟩ := targetDisc_re_bounds hzn
  obtain ⟨hm₁, hm₂⟩ := targetDisc_re_bounds hzm
  rcases lt_or_gt_of_ne hnm with h | h
  · have h' : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
    linarith
  · have h' : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
    linarith

theorem controlDisc_re_bound {n : ℕ} {z : ℂ} (hz : z ∈ controlDisc n) :
    z.re ≤ 3 * n - 2 := by
  have hnorm : ‖z - (-3 : ℂ)‖ ≤ 1 + 3 * n := by
    simpa only [controlDisc, mem_closedBall, dist_eq_norm] using hz
  have h := (le_abs_self (z - (-3 : ℂ)).re).trans
    ((Complex.abs_re_le_norm _).trans hnorm)
  change z.re - (-3) ≤ 1 + 3 * n at h
  linarith

theorem targetDisc_subset_controlDisc_interior {k n : ℕ} (hkn : k < n) :
    targetDisc k ⊆ interior (controlDisc n) := by
  intro z hz
  have hz' : dist z ((3 * k : ℝ) : ℂ) < 1 := hz
  have hc : dist (((3 * k : ℝ) : ℂ)) (-3) = 3 * k + 3 := by
    rw [dist_eq_norm]
    have heq : ((3 * k : ℝ) : ℂ) - (-3) = ((3 * k + 3 : ℝ) : ℂ) := by push_cast; ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hkn' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
  have hdist := dist_triangle z (((3 * k : ℝ) : ℂ)) (-3)
  rw [hc] at hdist
  exact ball_subset_interior_closedBall
    (show z ∈ ball (-3) (1 + 3 * n) from (by change dist z (-3) < _; linarith))

theorem controlDisc_mono : Monotone controlDisc := by
  intro n m hnm
  apply closedBall_subset_closedBall
  have h : (n : ℝ) ≤ m := by exact_mod_cast hnm
  linarith

theorem controlDisc_subset_interior_succ (n : ℕ) :
    controlDisc n ⊆ interior (controlDisc (n + 1)) := by
  intro z hz
  apply ball_subset_interior_closedBall
  have h : dist z (-3) ≤ 1 + 3 * n := hz
  change dist z (-3) < 1 + 3 * (n + 1 : ℕ)
  push_cast
  linarith

theorem add_three_mem_targetDisc {n : ℕ} {z : ℂ} (hz : z ∈ targetDisc n) :
    z + 3 ∈ targetDisc (n + 1) := by
  simp only [targetDisc, mem_ball, Nat.cast_add, Nat.cast_one]
  have hcenter : (((3 * (n + 1) : ℝ)) : ℂ) = ((3 * n : ℝ) : ℂ) + 3 := by
    push_cast
    ring
  rw [hcenter, dist_add_right]
  exact hz

theorem controlDisc_mem_nhds_eventually (z : ℂ) :
    ∀ᶠ n : ℕ in atTop, controlDisc n ∈ 𝓝 z := by
  obtain ⟨N, hN⟩ := exists_nat_gt (dist z (-3))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hz : z ∈ ball (-3 : ℂ) (1 + 3 * n) := by
    change dist z (-3) < _
    linarith
  exact Filter.mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall

theorem escapesUniformlyOn_of_targetDiscs (f : ℂ → ℂ) (K : Set ℂ)
    (hmap : ∀ n, MapsTo (f^[n]) K (targetDisc n)) :
    ComplexDynamics.EscapesUniformlyOn f K := by
  intro R
  obtain ⟨N, hN⟩ := exists_nat_gt (R + 1)
  filter_upwards [eventually_ge_atTop N] with n hn z hz
  have h := (targetDisc_re_bounds (hmap n hz)).1
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hre := (le_abs_self ((f^[n]) z).re).trans (Complex.abs_re_le_norm _)
  linarith

end EremenkosConjecture
