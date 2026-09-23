import Runge.PoleTopology

open Polynomial Filter Set
open scoped BigOperators Topology

namespace Runge

noncomputable def polynomialPolePartial (a : ℂ) (N : ℕ) : ℂ[X] :=
  C (-a⁻¹) * ∑ n ∈ Finset.range N, (X * C a⁻¹)^n

theorem polynomialPolePartial_eval (a z : ℂ) (N : ℕ) :
    (polynomialPolePartial a N).eval z = -a⁻¹ * ∑ n ∈ Finset.range N, (z/a)^n := by
  simp only [polynomialPolePartial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_finsetSum, Polynomial.eval_pow, Polynomial.eval_X, div_eq_mul_inv]

theorem polynomialPolePartial_remainder (a z : ℂ) (N : ℕ) (ha : a ≠ 0) (hz : z ≠ a) :
    (z-a)⁻¹ - (polynomialPolePartial a N).eval z = (z/a)^N / (z-a) := by
  have hrec : (z-a)⁻¹ + a⁻¹ = (z/a) * (z-a)⁻¹ := by
    field_simp [ha, sub_ne_zero.mpr hz]
    ring
  rw [polynomialPolePartial_eval]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    calc
      (z-a)⁻¹ - -a⁻¹ * ((∑ n ∈ Finset.range N, (z/a)^n) + (z/a)^N) =
          ((z-a)⁻¹ - -a⁻¹ * (∑ n ∈ Finset.range N, (z/a)^n)) + a⁻¹ * (z/a)^N := by ring
      _ = (z/a)^N * ((z-a)⁻¹ + a⁻¹) := by rw [ih]; ring
      _ = (z/a)^(N+1)/(z-a) := by rw [hrec, pow_succ]; ring

theorem exists_polynomialPolePartial_uniform (K : Set ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hK : ∀ z ∈ K, ‖z‖ ≤ r) (a : ℂ) (ha : r < ‖a‖) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ z ∈ K, ‖(z-a)⁻¹ - (polynomialPolePartial a N).eval z‖ < ε := by
  have ha0 : a ≠ 0 := norm_pos_iff.mp (hr.trans_lt ha)
  have hδ : 0 < ‖a‖-r := sub_pos.mpr ha
  have hq : 0 ≤ r/‖a‖ := div_nonneg hr (norm_nonneg a)
  have hq1 : r/‖a‖ < 1 := (div_lt_one (hr.trans_lt ha)).mpr ha
  have ht : Tendsto (fun N : ℕ => (r/‖a‖)^N/(‖a‖-r)) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).div_const (‖a‖-r)
  obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨N, fun z hz => lt_of_le_of_lt ?_ hN⟩
  have hza : z ≠ a := fun he => (not_le_of_gt ha) (he ▸ hK z hz)
  have hsep : ‖a‖-r ≤ ‖z-a‖ := by
    have htri : ‖a‖ ≤ ‖z-a‖+‖z‖ := by
      simpa only [dist_zero_right, dist_eq_norm, sub_zero, norm_sub_rev] using dist_triangle a z 0
    linarith [hK z hz]
  have hratio : ‖z/a‖ ≤ r/‖a‖ := by
    rw [norm_div]
    exact div_le_div_of_nonneg_right (hK z hz) (norm_nonneg a)
  rw [polynomialPolePartial_remainder a z N ha0 hza, norm_div, norm_pow]
  exact div_le_div₀ (pow_nonneg hq N)
    (pow_le_pow_left₀ (norm_nonneg _) hratio N) hδ hsep

/-- Every sufficiently distant pole lies in a closed algebra containing all
polynomial restrictions. -/
theorem poleKernel_mem_of_large_norm (K : Set ℂ) [CompactSpace K]
    (S : Subalgebra ℂ C(K, ℂ)) (hS : IsClosed (S : Set C(K, ℂ)))
    (hpoly : ∀ p : ℂ[X], polynomialMap K p ∈ S)
    (r : ℝ) (hr : 0 ≤ r) (hK : ∀ z ∈ K, ‖z‖ ≤ r)
    (a : ℂ) (ha : a ∉ K) (har : r < ‖a‖) : poleKernel K a ha ∈ S := by
  change poleKernel K a ha ∈ (S : Set C(K, ℂ))
  rw [← hS.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_polynomialPolePartial_uniform K r hr hK a har ε hε
  refine ⟨polynomialMap K (polynomialPolePartial a N), hpoly _, ?_⟩
  rw [dist_eq_norm, ContinuousMap.norm_lt_iff _ hε]
  exact fun z => hN z z.property

end Runge
