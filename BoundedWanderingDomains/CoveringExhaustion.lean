import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The numerical exhaustion step in the square-root covering construction

For an omitted point of modulus `r`, the normalised square-root construction
changes the derivative by the factor `2 * sqrt r / (1 + r)`. If the cumulative
derivatives remain bounded away from zero, the omitted-point radii tend to one.
This file proves that numerical step. It does not construct the covering maps
or prove convergence of those maps to a covering.
-/

open Set Filter
open scoped Topology

namespace AreaDeficit

theorem squareRootCovering_radii_tendsto_one {r d : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hr : ∀ n, 0 ≤ r n ∧ r n ≤ 1)
    (hd : ∀ n, c ≤ d n)
    (hstep : ∀ n, d (n + 1) ≤ (2 * Real.sqrt (r n) / (1 + r n)) * d n) :
    Tendsto r atTop (𝓝 1) := by
  have hs (n : ℕ) : 0 ≤ Real.sqrt (r n) ∧ Real.sqrt (r n) ≤ 1 :=
    ⟨Real.sqrt_nonneg _, (Real.sqrt_le_one).mpr (hr n).2⟩
  have hq (n : ℕ) : 2 * Real.sqrt (r n) / (1 + r n) ≤ 1 := by
    apply (div_le_one (by linarith [(hr n).1])).mpr
    nlinarith [sq_nonneg (1 - Real.sqrt (r n)), Real.sq_sqrt (hr n).1]
  have hanti : Antitone d := antitone_nat_of_succ_le fun n =>
    (hstep n).trans (mul_le_of_le_one_left (hc.le.trans (hd n)) (hq n))
  have hb : BddBelow (range d) := ⟨c, by rintro _ ⟨n, rfl⟩; exact hd n⟩
  have ht := tendsto_atTop_ciInf hanti hb
  have hgap : Tendsto (fun n => d n - d (n + 1)) atTop (𝓝 0) := by
    simpa only [sub_self, Function.comp_def] using ht.sub (ht.comp (tendsto_add_atTop_nat 1))
  have hbound (n : ℕ) : (1 - Real.sqrt (r n))^2 ≤ (2 / c) * (d n - d (n + 1)) := by
    have hden : 0 < 1 + r n := by linarith [(hr n).1]
    have hmul : (1 + r n) * d (n + 1) ≤ 2 * Real.sqrt (r n) * d n := by
      have hh := (mul_le_mul_of_nonneg_left (hstep n) hden.le)
      field_simp at hh
      nlinarith
    have hgapnonneg := sub_nonneg.mpr (hanti (Nat.le_succ n))
    have hcoef := mul_le_mul_of_nonneg_right (hd n) (sq_nonneg (1 - Real.sqrt (r n)))
    have hsq := Real.sq_sqrt (hr n).1
    have hrupper := (hr n).2
    have hmain : c * (1 - Real.sqrt (r n))^2 ≤ 2 * (d n - d (n + 1)) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hrupper) hgapnonneg,
        congrArg (fun t => d n * t) hsq]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    nlinarith [hmain]
  have htupper : Tendsto (fun n => (2 / c) * (d n - d (n + 1))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hgap
  have hsqzero : Tendsto (fun n => (1 - Real.sqrt (r n))^2) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htupper
      (fun n => sq_nonneg _) hbound
  have hzero : Tendsto (fun n => 1 - Real.sqrt (r n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq (sub_nonneg.mpr (hs _).2), Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hsqzero
  have hone : Tendsto (fun n => Real.sqrt (r n)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hzero
  simpa only [Real.sq_sqrt (hr _).1, one_pow] using hone.pow 2

end AreaDeficit
