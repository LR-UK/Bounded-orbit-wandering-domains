import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic

open Set
open scoped ENNReal ContDiff

namespace FunctionTheory

set_option autoImplicit false

/-- The sum of uniform norms of real derivatives in orders 0 through m.
The extended nonnegative real value records unbounded derivatives honestly.
For maps smooth on an open set this is the usual uniform C^m norm there. -/
noncomputable def finiteSmoothNormOn (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range (m + 1), ⨆ z ∈ U, ‖iteratedFDeriv ℝ n f z‖ₑ

/-- Every derivative norm is bounded by the sum defining the finite smooth norm. -/
theorem enorm_iteratedFDeriv_le_finiteSmoothNormOn
    (m : ℕ) (f : ℂ → ℂ) {U : Set ℂ} {n : ℕ} (hn : n ≤ m)
    {z : ℂ} (hz : z ∈ U) :
    ‖iteratedFDeriv ℝ n f z‖ₑ ≤ finiteSmoothNormOn m f U := by
  calc
    _ ≤ ⨆ w ∈ U, ‖iteratedFDeriv ℝ n f w‖ₑ :=
      le_iSup_of_le z (le_iSup_of_le hz le_rfl)
    _ ≤ finiteSmoothNormOn m f U := by
      unfold finiteSmoothNormOn
      exact Finset.single_le_sum
        (f := fun j => ⨆ w ∈ U, ‖iteratedFDeriv ℝ j f w‖ₑ)
        (fun _ _ => zero_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))

/-- A finite smooth norm bound implies each of the pointwise real bounds. -/
theorem norm_iteratedFDeriv_le_of_finiteSmoothNormOn_le
    {m : ℕ} {f : ℂ → ℂ} {U : Set ℂ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : finiteSmoothNormOn m f U ≤ ENNReal.ofReal δ)
    {n : ℕ} (hn : n ≤ m) {z : ℂ} (hz : z ∈ U) :
    ‖iteratedFDeriv ℝ n f z‖ ≤ δ := by
  have H := (enorm_iteratedFDeriv_le_finiteSmoothNormOn m f hn hz).trans hbound
  rw [← ofReal_norm] at H
  exact (ENNReal.ofReal_le_ofReal_iff hδ).mp H

/-- A common bound on the first m+1 derivatives controls their sum of suprema. -/
theorem finiteSmoothNormOn_le_of_uniform_bound
    {m : ℕ} {f : ℂ → ℂ} {U : Set ℂ} {δ : ℝ} (_hδ : 0 ≤ δ)
    (hbound : ∀ n ≤ m, ∀ z ∈ U, ‖iteratedFDeriv ℝ n f z‖ ≤ δ) :
    finiteSmoothNormOn m f U ≤ ENNReal.ofReal ((m + 1 : ℕ) * δ) := by
  calc
    finiteSmoothNormOn m f U ≤
        ∑ n ∈ Finset.range (m + 1), ENNReal.ofReal δ := by
      apply Finset.sum_le_sum
      intro n hn
      apply iSup_le
      intro z
      apply iSup_le
      intro hz
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hbound n (Nat.le_of_lt_succ
        (Finset.mem_range.mp hn)) z hz)
    _ = ENNReal.ofReal ((m + 1 : ℕ) * δ) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_natCast]

/-- A margin in each derivative bound gives a strict bound for the sum of
uniform norms; strict pointwise bounds without such a margin would not suffice. -/
theorem finiteSmoothNormOn_lt_of_uniform_margin
    {m : ℕ} {f : ℂ → ℂ} {U : Set ℂ} {ε : ℝ} (hε : 0 < ε)
    (hbound : ∀ n ≤ m, ∀ z ∈ U,
      ‖iteratedFDeriv ℝ n f z‖ ≤ ε / (2 * (m + 1 : ℕ))) :
    finiteSmoothNormOn m f U < ENNReal.ofReal ε := by
  have hden : (0 : ℝ) < 2 * (m + 1 : ℕ) := by positivity
  have H := finiteSmoothNormOn_le_of_uniform_bound (le_of_lt (div_pos hε hden)) hbound
  have hval : (m + 1 : ℕ) * (ε / (2 * (m + 1 : ℕ))) = ε / 2 := by
    have hm : (m + 1 : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [hval] at H
  exact H.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (half_lt_self hε))

end FunctionTheory
