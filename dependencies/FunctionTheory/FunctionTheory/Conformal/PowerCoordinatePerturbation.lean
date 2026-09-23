import TauCeti.Analysis.Complex.BranchLogRoot

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- A holomorphic branch of the `n`th root near one, normalized to take value one. -/
theorem exists_normalized_analytic_nth_root_at_one {n : ℕ} (hn : n ≠ 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 1 ∧ q 1 = 1 ∧
      ∀ᶠ w in 𝓝 (1 : ℂ), q w ^ n = w := by
  have hid : AnalyticAt ℂ (id : ℂ → ℂ) 1 := analyticAt_id
  have horder : analyticOrderAt (id : ℂ → ℂ) 1 = 0 :=
    hid.analyticOrderAt_eq_zero.mpr one_ne_zero
  obtain ⟨h, hh, hpow⟩ := (TauCeti.exists_eventuallyEq_pow_iff_dvd hid hn).mpr
    (by rw [horder]; exact dvd_zero _)
  have hp1 : h 1 ^ n = 1 := hpow.self_of_nhds.symm
  have hh1 : h 1 ≠ 0 := by
    intro hz
    simp only [hz, zero_pow hn] at hp1
    exact zero_ne_one hp1
  let q : ℂ → ℂ := fun w => h w / h 1
  refine ⟨q, hh.div analyticAt_const hh1, div_self hh1, ?_⟩
  filter_upwards [hpow] with w hw
  simp only [q, div_pow, hp1, div_one]
  exact hw.symm

/-- The normalized root branch can be kept uniformly as close to one as
desired by reducing its disk of definition. -/
theorem exists_controlled_analytic_nth_root {n : ℕ} (hn : n ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∃ q : ℂ → ℂ,
      AnalyticOnNhd ℂ q (ball 1 ρ) ∧ q 1 = 1 ∧
      ∀ w ∈ ball 1 ρ, q w ^ n = w ∧ ‖q w - 1‖ < ε := by
  obtain ⟨q, hq, hq1, hpow⟩ := exists_normalized_analytic_nth_root_at_one hn
  have hnear : ∀ᶠ w in 𝓝 (1 : ℂ), ‖q w - 1‖ < ε := by
    simpa only [hq1, mem_ball, dist_eq_norm] using
      hq.continuousAt.tendsto.eventually (ball_mem_nhds (q 1) hε)
  obtain ⟨ρ, hρ, H⟩ := Metric.nhds_basis_ball.eventually_iff.mp
    (hq.eventually_analyticAt.and (hpow.and hnear))
  exact ⟨ρ, hρ, q, fun w hw => (H hw).1, hq1, fun w hw => (H hw).2⟩

/-- A small perturbation of the nonvanishing unit factor of a power coordinate
has a holomorphic power coordinate uniformly close to the original one. -/
theorem exists_close_power_coordinate_of_close_unit
    {U : Set ℂ} {α u : ℂ → ℂ} {c : ℂ} {n : ℕ} (hn : n ≠ 0)
    (hα : AnalyticOnNhd ℂ α U) (hu : AnalyticOnNhd ℂ u U)
    {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hlower : ∀ z ∈ U, m ≤ ‖u z‖) (hupper : ∀ z ∈ U, ‖α z‖ ≤ M)
    (hfactor : ∀ z ∈ U, α z ^ n = (z - c) ^ n * u z)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ v : ℂ → ℂ, AnalyticOnNhd ℂ v U →
      (∀ z ∈ U, ‖v z - u z‖ < δ) →
      ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β U ∧
        (∀ z ∈ U, ‖β z - α z‖ < ε ∧ β z ^ n = (z - c) ^ n * v z) ∧
        (α c = 0 → β c = 0) := by
  have hMp : 0 < M + 1 := by linarith
  obtain ⟨ρ, hρ, q, hq, hq1, Hq⟩ := exists_controlled_analytic_nth_root hn (div_pos hε hMp)
  refine ⟨m * ρ, mul_pos hm hρ, ?_⟩
  intro v hv hclose
  have hu0 : ∀ z ∈ U, u z ≠ 0 :=
    fun z hz => norm_pos_iff.mp (hm.trans_le (hlower z hz))
  have hratio : ∀ z ∈ U, v z / u z ∈ ball 1 ρ := by
    intro z hz
    have heq : v z / u z - 1 = (v z - u z) / u z := by field_simp [hu0 z hz]
    rw [mem_ball, dist_eq_norm, heq, norm_div]
    apply (div_lt_iff₀ (hm.trans_le (hlower z hz))).mpr
    exact (hclose z hz).trans_le (by nlinarith [hlower z hz])
  let β : ℂ → ℂ := fun z => α z * q (v z / u z)
  have hβ : AnalyticOnNhd ℂ β U := by
    intro z hz
    have hvu : AnalyticAt ℂ (fun w => v w / u w) z :=
      (hv z hz).div (hu z hz) (hu0 z hz)
    have hc : AnalyticAt ℂ (fun w => q (v w / u w)) z :=
      AnalyticAt.comp (f := fun w => v w / u w) (g := q) (x := z)
        (hq _ (hratio z hz)) hvu
    exact (hα z hz).mul hc
  refine ⟨β, hβ, ?_, ?_⟩
  · intro z hz
    obtain ⟨hpow, hnorm⟩ := Hq _ (hratio z hz)
    constructor
    · have heq : β z - α z = α z * (q (v z / u z) - 1) := by dsimp [β]; ring
      rw [heq, norm_mul]
      calc
        ‖α z‖ * ‖q (v z / u z) - 1‖ ≤ (M + 1) * ‖q (v z / u z) - 1‖ :=
          mul_le_mul_of_nonneg_right (by linarith [hupper z hz]) (norm_nonneg _)
        _ < (M + 1) * (ε / (M + 1)) := mul_lt_mul_of_pos_left hnorm hMp
        _ = ε := by field_simp
    · dsimp [β]
      rw [mul_pow, hpow, hfactor z hz]
      field_simp [hu0 z hz]
  · intro hc
    simp only [β, hc, zero_mul]

end FunctionTheory
