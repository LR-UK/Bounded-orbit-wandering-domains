import EremenkosConjecture.ScaffoldingApproximation

/-! # Real-part bounds for the Section 4 return branches -/

open Set Function Complex

namespace EremenkosConjecture.Scaffolding

theorem re_error_of_close_affine {f : ℂ → ℂ} {z : ℂ}
    (hclose : ‖f z - 5 * z‖ ≤ 1 / 100) : |(f z).re - 5 * z.re| ≤ (1 / 100 : ℝ) := by
  simpa using (abs_re_le_norm (f z - 5 * z)).trans hclose

theorem abs_re_expansion_from_half {f : ℂ → ℂ} {z : ℂ}
    (hclose : ‖f z - 5 * z‖ ≤ 1 / 100) (hz : 1 / 2 ≤ |z.re|) :
    2 * |z.re| ≤ |(f z).re| := by
  have he := re_error_of_close_affine hclose
  have hn := abs_sub_abs_le_abs_sub (5 * z.re) (f z).re
  rw [abs_sub_comm, abs_mul] at hn
  norm_num at hn
  linarith

theorem abs_re_iterate_lower_bound {f : ℂ → ℂ} {z : ℂ} {n : ℕ} {R : ℝ}
    (hR : 1 / 2 ≤ R) (hz : R ≤ |z.re|)
    (hclose : ∀ k < n, ‖f ((f^[k]) z) - 5 * (f^[k]) z‖ ≤ 1 / 100) :
    ∀ k ≤ n, R ≤ |((f^[k]) z).re| := by
  intro k hk
  induction k with
  | zero => exact hz
  | succ k ih =>
      have hi := ih (by omega)
      have he := abs_re_expansion_from_half (hclose k (by omega)) (hR.trans hi)
      rw [iterate_succ_apply']
      linarith [abs_nonneg ((f^[k]) z).re]

theorem abs_re_preimage_lt_half {f : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (hclose : ∀ k < n, ‖f ((f^[k]) z) - 5 * (f^[k]) z‖ ≤ 1 / 100)
    (hfinal : |((f^[n]) z).re| < 1 / 2) : |z.re| < 1 / 2 := by
  by_contra h
  exact (not_lt_of_ge (abs_re_iterate_lower_bound le_rfl (le_of_not_gt h) hclose n le_rfl)) hfinal

theorem re_iterate_lower_bound {f : ℂ → ℂ} {z : ℂ} {n : ℕ} {M : ℝ}
    (hM : 0 ≤ M) (hz : -M ≤ z.re)
    (hclose : ∀ k < n, ‖f ((f^[k]) z) - 5 * (f^[k]) z‖ ≤ 1 / 100) :
    -(6 : ℝ) ^ n * (M + 1) ≤ ((f^[n]) z).re := by
  have hbound (k : ℕ) (hk : k ≤ n) : -(6 : ℝ) ^ k * (M + 1) ≤ ((f^[k]) z).re := by
    induction k with
    | zero => simpa using (show -(M + 1) ≤ z.re by linarith)
    | succ k ih =>
        have hi := ih (by omega)
        have he := (abs_le.mp (re_error_of_close_affine (hclose k (by omega)))).1
        have hp : (1 : ℝ) ≤ 6 ^ k := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 6)
        have hpM : (1 : ℝ) ≤ 6 ^ k * (M + 1) := by nlinarith
        rw [iterate_succ_apply', pow_succ]
        nlinarith
  exact hbound n le_rfl

theorem re_preimage_far_left {f : ℂ → ℂ} {z : ℂ} {n : ℕ} {M : ℝ}
    (hM : 0 ≤ M)
    (hclose : ∀ k < n, ‖f ((f^[k]) z) - 5 * (f^[k]) z‖ ≤ 1 / 100)
    (hfinal : ((f^[n]) z).re < -(6 : ℝ) ^ n * (M + 1)) : z.re < -M := by
  by_contra h
  exact (not_lt_of_ge (re_iterate_lower_bound hM (le_of_not_gt h) hclose)) hfinal

end EremenkosConjecture.Scaffolding
