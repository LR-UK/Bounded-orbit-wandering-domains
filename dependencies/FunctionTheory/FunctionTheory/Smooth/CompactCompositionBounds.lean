import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic

open Set Function Filter
open scoped Topology ContDiff

namespace FunctionTheory

set_option autoImplicit false

/-- Right composition by a fixed smooth homeomorphism has a uniform finite
derivative bound for functions supported in a fixed compact set. The fixed
map need not have globally bounded derivatives. -/
theorem exists_uniform_comp_derivative_bound
    (Θ : ℂ ≃ₜ ℂ) (m : ℕ) (hΘ : ContDiff ℝ m (Θ : ℂ → ℂ))
    {L : Set ℂ} (hL : IsCompact L) :
    ∃ M > 0, ∀ u : ℂ → ℂ, ContDiff ℝ m u → tsupport u ⊆ L →
      ∀ δ ≥ 0, (∀ n ≤ m, ∀ z, ‖iteratedFDeriv ℝ n u z‖ ≤ δ) →
      ∀ n ≤ m, ∀ z, ‖iteratedFDeriv ℝ n (u ∘ Θ) z‖ ≤ M * δ := by
  classical
  let S := Θ.symm '' L
  have hS : IsCompact S := hL.image Θ.symm.continuous
  have hmem : ∀ z, z ∈ S ↔ Θ z ∈ L := by
    intro z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa only [Θ.apply_symm_apply] using hw
    · intro hz
      exact ⟨Θ z, hz, Θ.symm_apply_apply z⟩
  have Hbounds : ∀ i : Fin (m + 1), ∃ C : ℝ,
      ∀ z ∈ S, ‖iteratedFDeriv ℝ (i : ℕ) (Θ : ℂ → ℂ) z‖ ≤ C := by
    intro i
    exact hS.exists_bound_of_continuousOn
      (hΘ.continuous_iteratedFDeriv (by exact_mod_cast Nat.le_of_lt_succ i.isLt)).continuousOn
  choose B HB using Hbounds
  let C : ℝ := 1 + ∑ i : Fin (m + 1), max 0 (B i)
  have hC1 : 1 ≤ C := by
    have H := Finset.sum_nonneg (fun (i : Fin (m + 1)) (_ : i ∈ Finset.univ) => le_max_left 0 (B i))
    dsimp [C]
    linarith
  have hBC : ∀ i : Fin (m + 1), B i ≤ C := by
    intro i
    have H := Finset.single_le_sum
      (fun (j : Fin (m + 1)) (_ : j ∈ Finset.univ) => le_max_left 0 (B j))
      (Finset.mem_univ i)
    have Hi := le_max_right 0 (B i)
    dsimp [C]
    linarith
  have HD : ∀ i, 1 ≤ i → i ≤ m → ∀ z ∈ S,
      ‖iteratedFDeriv ℝ i (Θ : ℂ → ℂ) z‖ ≤ C ^ i := by
    intro i hi him z hz
    have H := (HB ⟨i, Nat.lt_succ_of_le him⟩ z hz).trans
      (hBC ⟨i, Nat.lt_succ_of_le him⟩)
    exact H.trans (by simpa only [pow_one] using pow_le_pow_right₀ hC1 hi)
  let b : ℕ → ℝ := fun n => n.factorial * C ^ n
  have hb : ∀ n, 0 ≤ b n := fun n => mul_nonneg (by positivity)
    (pow_nonneg (le_trans zero_le_one hC1) n)
  let M : ℝ := 1 + ∑ i ∈ Finset.range (m + 1), b i
  have hM : 0 < M := by
    have H := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range (m + 1)) => hb i)
    dsimp [M]
    linarith
  have HbM : ∀ n ≤ m, b n ≤ M := by
    intro n hn
    have H := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (m + 1)) => hb i)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
    dsimp [M]
    linarith
  refine ⟨M, hM, ?_⟩
  intro u hu huL δ hδ Hδ n hn z
  by_cases hz : z ∈ S
  · calc
      ‖iteratedFDeriv ℝ n (u ∘ Θ) z‖ ≤ n.factorial * δ * C ^ n :=
        norm_iteratedFDeriv_comp_le hu hΘ (by exact_mod_cast hn) z
          (fun i hi => Hδ i (hi.trans hn) (Θ z))
          (fun i hi hin => HD i hi (hin.trans hn) z hz)
      _ = b n * δ := by dsimp [b]; ring
      _ ≤ M * δ := mul_le_mul_of_nonneg_right (HbM n hn) hδ
  · have hsupp : tsupport (u ∘ Θ) ⊆ S := by
      apply closure_minimal _ hS.isClosed
      intro w hw
      apply (hmem w).mpr
      exact huL (subset_closure hw)
    have hzero : iteratedFDeriv ℝ n (u ∘ Θ) z = 0 := by
      apply notMem_support.mp
      intro H
      exact hz (hsupp (support_iteratedFDeriv_subset n H))
    rw [hzero, norm_zero]
    exact mul_nonneg hM.le hδ

end FunctionTheory
