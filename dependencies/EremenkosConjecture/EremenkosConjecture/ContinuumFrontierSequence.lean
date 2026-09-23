import EremenkosConjecture.ContinuumRegionGeometry

open Set Metric Complex Filter
open scoped Topology

namespace EremenkosConjecture

/-- The straight top edge gives an explicit sequence on the boundary
tending to infinity. This supplies the transcendentality witness in the limit. -/
theorem ContinuumNeighbourhoods.exists_frontier_sequence {X : Set ℂ} {ζ : ℂ} {r : ℝ}
    (D : ContinuumNeighbourhoods X ζ r) (i : ℕ) :
    ∃ u : ℕ → ℂ, (∀ n, u n ∈ frontier (D.region i)) ∧
      Tendsto (fun n => ‖u n‖) atTop atTop := by
  obtain ⟨A, _, htail⟩ := D.exists_common_tail
  let u : ℕ → ℂ := fun n => ⟨A + 1 + n, ζ.im + D.width i⟩
  have huA (n : ℕ) : A < (u n).re := by
    change A < A + 1 + n
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hu (n : ℕ) : u n ∈ D.region i := by
    apply (htail i (u n) (huA n)).1.mpr
    change |ζ.im + D.width i - ζ.im| ≤ D.width i
    simp only [add_sub_cancel_left, abs_of_pos (D.positive i), le_refl]
  refine ⟨u, fun n => ⟨(D.geometry i).1.isClosed.closure_eq.symm ▸ hu n, ?_⟩, ?_⟩
  · intro hn
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hn)
    let w := u n + (ε / 2 : ℝ) * I
    have hw : w ∈ D.region i := by
      apply hball
      rw [mem_ball, dist_eq_norm]
      change ‖u n + (ε / 2 : ℝ) * I - u n‖ < ε
      rw [add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real,
        Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      exact half_lt_self hε
    have hwre : w.re = (u n).re := by
      simp only [w, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero]
    have hi := (htail i w (by rw [hwre]; exact huA n)).1.mp hw
    have hwi : w.im - ζ.im = D.width i + ε / 2 := by
      simp only [w, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_one, zero_mul, add_zero, u]
      ring
    rw [hwi, abs_of_pos (by linarith [D.positive i])] at hi
    linarith
  · apply Filter.tendsto_atTop.mpr
    intro b
    obtain ⟨N, hN⟩ := exists_nat_ge (b - A - 1)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnat : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hre : b ≤ (u n).re := by change b ≤ A + 1 + n; linarith
    exact hre.trans (re_le_norm (u n))

end EremenkosConjecture
