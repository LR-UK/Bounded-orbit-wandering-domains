import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

open Set Function Filter
open scoped Topology ContDiff

namespace FunctionTheory

set_option autoImplicit false

/-- Multiplication by a smooth cutoff supported inside the working domain
gives a globally smooth function, regardless of the other factor's values
outside that domain. -/
theorem contDiff_cutoff_smul
    {U : Set ℂ} (hU : IsOpen U) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχU : tsupport χ ⊆ U) {g : ℂ → ℂ} (hg : ContDiffOn ℝ ∞ g U) :
    ContDiff ℝ ∞ (fun z => χ z • g z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport χ
  · exact hχ.contDiffAt.smul (hg.contDiffAt (hU.mem_nhds (hχU hz)))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
    simp only [Pi.zero_apply] at hw
    simp [hw]

/-- A fixed compactly supported smooth cutoff acts with a uniform finite
derivative bound on functions smooth on its working neighbourhood. -/
theorem exists_uniform_cutoff_derivative_bound
    {U : Set ℂ} (hU : IsOpen U) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) (m : ℕ) :
    ∃ M > 0, ∀ g : ℂ → ℂ, ContDiffOn ℝ ∞ g U →
      ∀ δ ≥ 0, (∀ n ≤ m, ∀ z ∈ U, ‖iteratedFDeriv ℝ n g z‖ ≤ δ) →
      ∀ n ≤ m, ∀ z, ‖iteratedFDeriv ℝ n (fun w => χ w • g w) z‖ ≤ M * δ := by
  obtain ⟨C, hC0, HC⟩ := hχc.exists_bound_iteratedFDeriv hχ m
  let M : ℝ := 2 ^ m * (C + 1)
  have hM : 0 < M := mul_pos (pow_pos (by norm_num) m) (by linarith)
  refine ⟨M, hM, ?_⟩
  intro g hg δ hδ Hδ n hn z
  let u : ℂ → ℂ := fun w => χ w • g w
  have husupp : tsupport u ⊆ tsupport χ := by
    apply closure_mono
    intro w hw
    by_contra hwχ
    have hw0 : χ w = 0 := notMem_support.mp hwχ
    exact hw (by simp [u, hw0])
  by_cases hz : z ∈ tsupport χ
  · have hzU := hχU hz
    have HCder : ∀ (q : ℂ → ℂ) (j : ℕ),
        iteratedFDerivWithin ℝ j q U z = iteratedFDeriv ℝ j q z :=
      fun q j => iteratedFDerivWithin_of_isOpen j hU hzU
    have HRder : ∀ (q : ℂ → ℝ) (j : ℕ),
        iteratedFDerivWithin ℝ j q U z = iteratedFDeriv ℝ j q z :=
      fun q j => iteratedFDerivWithin_of_isOpen j hU hzU
    have H := norm_iteratedFDerivWithin_smul_le hχ.contDiffOn hg hU.uniqueDiffOn hzU
      (n := n) (by simp)
    simp only [HCder, HRder] at H
    have Hsum :
        (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ z‖ *
          ‖iteratedFDeriv ℝ (n - i) g z‖) ≤ 2 ^ n * C * δ := by
      calc
        _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C * δ := by
          apply Finset.sum_le_sum
          intro i hi
          have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (HC i (hin.trans hn) z) (by positivity))
            (Hδ (n - i) ((Nat.sub_le n i).trans hn) z hzU)
            (norm_nonneg _) (mul_nonneg (by positivity) hC0)
        _ = 2 ^ n * C * δ := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          have hs : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
            exact_mod_cast Nat.sum_range_choose n
          rw [hs]
    have hcoef : (2 : ℝ) ^ n * C ≤ M := by
      calc
        (2 : ℝ) ^ n * C ≤ 2 ^ m * C :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hC0
        _ ≤ 2 ^ m * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact (H.trans Hsum).trans (mul_le_mul_of_nonneg_right hcoef hδ)
  · have hzero : iteratedFDeriv ℝ n u z = 0 := by
      apply notMem_support.mp
      intro h
      exact hz (husupp (support_iteratedFDeriv_subset n h))
    change ‖iteratedFDeriv ℝ n u z‖ ≤ M * δ
    rw [hzero, norm_zero]
    exact mul_nonneg hM.le hδ

end FunctionTheory
