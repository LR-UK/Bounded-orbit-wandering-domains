import EremenkosConjecture.ScaffoldingGeometry
import ComplexDynamics.Bungee
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Orbit consequences of the Section 7 return schedule -/

open Set Metric Complex Function Filter ComplexDynamics
open scoped Topology

namespace EremenkosConjecture.Scaffolding

theorem strictMono_returnTime : StrictMono returnTime := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [returnTime_succ]
  omega

theorem nat_le_returnTime (j : ℕ) : j ≤ returnTime j := by
  induction j with
  | zero => simp
  | succ j hj => rw [returnTime_succ]; omega

theorem exists_returnTime_interval {n : ℕ} (hn : 1 ≤ n) :
    ∃ j : ℕ, returnTime j + 1 ≤ n ∧ n ≤ returnTime (j + 1) := by
  have hex : ∃ j, n ≤ returnTime (j + 1) := ⟨n, (Nat.le_succ n).trans (nat_le_returnTime _)⟩
  let j := Nat.find hex
  refine ⟨j, ?_, Nat.find_spec hex⟩
  cases hj : j with
  | zero => simpa [hj] using hn
  | succ k =>
      have hminimal := Nat.find_min hex (show k < Nat.find hex from by omega)
      omega

theorem tendsto_norm_of_targetStrips {u : ℕ → ℂ} (hu : ∀ j, u j ∈ targetStrip j) :
    Tendsto (fun j => ‖u j‖) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro R
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * R)
  filter_upwards [eventually_ge_atTop N] with j hj
  have hjR : 4 * R < (j : ℝ) := hN.trans_le (by exact_mod_cast hj)
  have hheight := nat_le_height j
  have him := (hu j).1
  have hnorm := Complex.im_le_norm (u j)
  linarith

/-- Condition (F) controls all times after the first return, not merely a
subsequence of iterates. -/
theorem mem_escapingSet_of_return_blocks {f : ℂ → ℂ} {z : ℂ}
    (hblocks : ∀ j n : ℕ, returnTime j + 1 ≤ n → n ≤ returnTime (j + 1) →
      (j : ℝ) ≤ |((f^[n]) z).re|) : z ∈ escapingSet f := by
  apply Filter.tendsto_atTop.2
  intro R
  obtain ⟨J, hJ⟩ := exists_nat_gt R
  filter_upwards [eventually_ge_atTop (returnTime J + 1)] with n hn
  obtain ⟨j, hjlo, hjhi⟩ := exists_returnTime_interval (by omega : 1 ≤ n)
  have hJj : J ≤ j := by
    by_contra h
    have hle := strictMono_returnTime.monotone (show j + 1 ≤ J by omega)
    omega
  have hcast : (J : ℝ) ≤ (j : ℝ) := by exact_mod_cast hJj
  exact (hJ.le.trans hcast).trans
    ((hblocks j n hjlo hjhi).trans (Complex.abs_re_le_norm _))

theorem norm_le_three_of_sourceStrip_zero {z : ℂ} (hz : z ∈ sourceStrip 0)
    (hre : |z.re| ≤ 1) : ‖z‖ ≤ 3 := by
  have hi : 1 < z.im ∧ z.im < 2 := by
    norm_num [sourceStrip, height] at hz
    constructor <;> linarith [hz.1, hz.2]
  have hnorm := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_pos (by linarith : 0 < z.im)] at hnorm
  linarith

theorem strictMono_excursionTime : StrictMono (fun j => returnTime (j + 1)) :=
  strictMono_returnTime.comp (fun _ _ h => Nat.add_lt_add_right h 1)

theorem strictMono_firstReturnTime : StrictMono (fun j => returnTime j + 1) :=
  fun _ _ h => Nat.add_lt_add_right (strictMono_returnTime h) 1

theorem tendsto_norm_of_targetStrip_excursions {f : ℂ → ℂ} {z : ℂ}
    (hexc : ∀ j, (f^[returnTime j]) z ∈ targetStrip j) :
    Tendsto (fun j => ‖(f^[returnTime j]) z‖) atTop atTop :=
  tendsto_norm_of_targetStrips hexc

theorem mem_bungeeSet_of_strip_returns {f : ℂ → ℂ} {z : ℂ}
    (hexc : ∀ j, (f^[returnTime j]) z ∈ targetStrip j)
    (hreturn : ∀ j, (f^[returnTime j + 1]) z ∈ sourceStrip 0)
    (hre : ∀ᶠ j in atTop, |((f^[returnTime j + 1]) z).re| ≤ 1) :
    z ∈ bungeeSet f := by
  apply mem_bungeeSet_of_subsequences (tendsto_norm_of_targetStrip_excursions hexc)
    strictMono_firstReturnTime.tendsto_atTop
  exact hre.mono fun j hj => norm_le_three_of_sourceStrip_zero (hreturn j) hj

end EremenkosConjecture.Scaffolding
