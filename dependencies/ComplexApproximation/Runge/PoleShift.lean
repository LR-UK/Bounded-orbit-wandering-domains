import Runge.Rational
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# A quantitative step in moving a pole

The finite geometric expansion moves a simple pole at `a` to a pole at `b`.
Its exact remainder gives a uniform bound whenever the geometric ratio is
uniformly smaller than one and the original pole stays separated from the set.
-/

open scoped BigOperators Topology
open Filter

namespace Runge

/-- The first `N` terms of the expansion about the new pole `b`. -/
noncomputable def polePartial (a b : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  (z - b)⁻¹ * ∑ n ∈ Finset.range N, ((a - b) / (z - b)) ^ n

/-- The resolvent identity, with the sign chosen for a geometric expansion. -/
theorem inv_sub_difference (a b z : ℂ) (ha : z ≠ a) (hb : z ≠ b) :
    (z - a)⁻¹ - (z - b)⁻¹ = ((a - b) / (z - b)) * (z - a)⁻¹ := by
  field_simp [sub_ne_zero.mpr ha, sub_ne_zero.mpr hb]
  ring

/-- Exact remainder after moving a pole and keeping `N` geometric terms. -/
theorem polePartial_remainder (a b z : ℂ) (N : ℕ)
    (ha : z ≠ a) (hb : z ≠ b) :
    (z - a)⁻¹ - polePartial a b N z =
      ((a - b) / (z - b)) ^ N / (z - a) := by
  induction N with
  | zero => simp [polePartial]
  | succ N ih =>
    calc
      (z - a)⁻¹ - polePartial a b (N + 1) z =
          ((z - a)⁻¹ - polePartial a b N z) -
            (z - b)⁻¹ * ((a - b) / (z - b)) ^ N := by
              simp only [polePartial, Finset.sum_range_succ]
              ring
      _ = ((a - b) / (z - b)) ^ N * ((z - a)⁻¹ - (z - b)⁻¹) := by
        rw [ih]
        ring
      _ = ((a - b) / (z - b)) ^ (N + 1) / (z - a) := by
        rw [inv_sub_difference a b z ha hb, pow_succ]
        ring

/-- Uniform error bound for one legal pole movement. -/
theorem norm_polePartial_error_le (a b z : ℂ) (N : ℕ)
    (δ q : ℝ) (hδ : 0 < δ) (hq : 0 ≤ q)
    (hsep : δ ≤ ‖z - a‖) (hb : z ≠ b)
    (hratio : ‖(a - b) / (z - b)‖ ≤ q) :
    ‖(z - a)⁻¹ - polePartial a b N z‖ ≤ q ^ N / δ := by
  have ha : z ≠ a := by
    intro h
    subst z
    simp only [sub_self, norm_zero] at hsep
    exact (not_le_of_gt hδ) hsep
  rw [polePartial_remainder a b z N ha hb, norm_div, norm_pow]
  exact div_le_div₀ (pow_nonneg hq N) (pow_le_pow_left₀ (norm_nonneg _) hratio N)
    hδ hsep

/-- The remainder tends to zero uniformly on any set with uniform separation
and a uniform geometric-ratio bound strictly below one. -/
theorem exists_polePartial_uniform_error {K : Set ℂ} (a b : ℂ)
    (δ q : ℝ) (hδ : 0 < δ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hsep : ∀ z ∈ K, δ ≤ ‖z - a‖)
    (hb : b ∉ K) (hratio : ∀ z ∈ K, ‖(a - b) / (z - b)‖ ≤ q)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ z ∈ K, ‖(z - a)⁻¹ - polePartial a b N z‖ < ε := by
  have ht : Tendsto (fun N : ℕ => q ^ N / δ) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).div_const δ
  obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨N, fun z hz => ?_⟩
  have hzb : z ≠ b := fun h => hb (h ▸ hz)
  exact (norm_polePartial_error_le a b z N δ q hδ hq (hsep z hz)
    hzb (hratio z hz)).trans_lt hN

/-- Every truncation is a rational function nonvanishing in its denominator on
`K`; its formula uses only the new pole `b`. -/
theorem polePartial_isRationalOn {K : Set ℂ} (a b : ℂ) (N : ℕ)
    (hb : b ∉ K) : IsRationalOn K (polePartial a b N) := by
  have hkernel : IsRationalOn K (fun z => (z - b)⁻¹) := by
    simpa only [one_div] using IsRationalOn.simplePole hb 1
  have hratio := IsRationalOn.simplePole hb (a - b)
  exact hkernel.mul (IsRationalOn.sum (Finset.range N)
    (fun n z => ((a - b) / (z - b)) ^ n) (fun n _ => hratio.pow n))

/-- A legal pole movement: if the displacement is smaller than a uniform
clearance of the new pole from `K`, finite geometric truncations approximate
the original simple-pole kernel uniformly on `K`. -/
theorem pole_shift_uniform_approximation {K : Set ℂ} (a b : ℂ)
    (d : ℝ) (hd : 0 < d) (hmove : ‖a - b‖ < d)
    (hclear : ∀ z ∈ K, d ≤ ‖z - b‖) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, IsRationalOn K (polePartial a b N) ∧
      ∀ z ∈ K, ‖(z - a)⁻¹ - polePartial a b N z‖ < ε := by
  have hb : b ∉ K := by
    intro hb
    have h := hclear b hb
    simp only [sub_self, norm_zero] at h
    exact (not_le_of_gt hd) h
  have hsep : ∀ z ∈ K, d - ‖a - b‖ ≤ ‖z - a‖ := by
    intro z hz
    have htri : ‖z - b‖ ≤ ‖z - a‖ + ‖a - b‖ := by
      simpa only [dist_eq_norm] using dist_triangle z a b
    exact sub_le_iff_le_add.mpr ((hclear z hz).trans htri)
  have hratio : ∀ z ∈ K, ‖(a - b) / (z - b)‖ ≤ ‖a - b‖ / d := by
    intro z hz
    rw [norm_div]
    exact div_le_div₀ (norm_nonneg _) le_rfl hd (hclear z hz)
  obtain ⟨N, hN⟩ := exists_polePartial_uniform_error a b
    (d - ‖a - b‖) (‖a - b‖ / d) (sub_pos.mpr hmove)
    (div_nonneg (norm_nonneg _) hd.le) ((div_lt_one hd).mpr hmove)
    hsep hb hratio ε hε
  exact ⟨N, polePartial_isRationalOn a b N hb, hN⟩

end Runge
