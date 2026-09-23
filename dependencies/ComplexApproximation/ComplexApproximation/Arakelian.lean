import ComplexApproximation.ArakelianStep
import ComplexApproximation.HolomorphicLimit
import ComplexApproximation.Topology.Arakelian
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Neighbourhood-holomorphic Arakelian approximation

This is the Runge-based case of Rosay and Rudin's 1989 Monthly proof. The
function is holomorphic near the closed approximation set, and the geometric
hypothesis is stated explicitly in its bounded-exhaustion-holes formulation.
-/

open Set Metric Filter Bornology
open scoped Topology

namespace ComplexApproximation

/-- Uniform entire approximation on a closed Arakelian set for a function
holomorphic on an open neighbourhood. -/
theorem arakelian_approximation (E : Set ℂ) (hE : IsArakelian E)
    (U : Set ℂ) (hU : IsOpen U) (hEU : E ⊆ U)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z ∈ E, ‖g z - f z‖ < ε := by
  classical
  let A := arakelianExhaustion E
  let S (n : ℕ) := {g : ℂ → ℂ // ∃ V : Set ℂ,
    IsOpen V ∧ A n ⊆ V ∧ AnalyticOnNhd ℂ g V}
  let δ : ℕ → ℝ := fun n => (ε / 4) * (1 / 2 : ℝ) ^ n
  have hδpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδsum : Summable δ := summable_geometric_two.mul_left (ε / 4)
  have hδtotal : ∑' n, δ n = ε / 2 := by
    dsimp [δ]
    rw [tsum_mul_left, tsum_geometric_two]
    ring
  let initial : S 0 := ⟨f, U, hU, by simpa [A] using hEU, hf⟩
  have hstep (n : ℕ) (s : S n) :
      ∃ t : S (n + 1), ∀ z ∈ A n, ‖t.val z - s.val z‖ < δ n := by
    obtain ⟨V, hV, hAV, hs⟩ := s.property
    obtain ⟨g, W, hW, hAW, hg, herr⟩ :=
      exists_holomorphic_extension_of_bounded_difference (A n) (A (n + 1))
        (isClosed_arakelianExhaustion hE.isClosed n)
        (noBoundedComplementComponents_arakelianExhaustion hE.noBoundedComplementComponents n)
        (hE.isBounded_exhaustion_succ_diff n) V hV hAV s.val hs (δ n) (hδpos n)
    exact ⟨⟨g, W, hW, hAW, hg⟩, herr⟩
  choose next hnext using hstep
  let stages : (n : ℕ) → S n := Nat.rec initial next
  let F : ℕ → ℂ → ℂ := fun n => (stages n).val
  have hF0 : F 0 = f := rfl
  have hstepF (n : ℕ) (z : ℂ) (hz : z ∈ A n) :
      ‖F (n + 1) z - F n z‖ ≤ δ n := (hnext n (stages n) z hz).le
  have hFA (n : ℕ) : ∀ z ∈ A n, DifferentiableAt ℂ (F n) z := by
    obtain ⟨V, _, hAV, hF⟩ := (stages n).property
    intro z hz
    exact (hF z (hAV hz)).differentiableAt
  have hball (z : ℂ) : ∃ N : ℕ, z ∈ ball 0 (N : ℝ) ∧
      ∀ n ≥ N, ball 0 (N : ℝ) ⊆ A n := by
    obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
    have hN0 : N ≠ 0 := by
      intro hzero
      simp only [hzero, Nat.cast_zero] at hN
      exact (not_lt_of_ge (norm_nonneg z)) hN
    refine ⟨N, mem_ball_zero_iff.mpr hN, ?_⟩
    intro n hn
    exact ball_subset_closedBall.trans
      ((closedBall_subset_arakelianExhaustion E hN0).trans (arakelianExhaustion_mono E hn))
  obtain ⟨g, hg, hconv⟩ := exists_entire_limit_of_eventually_holomorphic_corrections F
    (by
      intro z
      obtain ⟨N, hz, hN⟩ := hball z
      refine ⟨ball 0 (N : ℝ), isOpen_ball, hz, ?_⟩
      filter_upwards [eventually_ge_atTop N] with n hn
      exact fun w hw => (hFA n w (hN n hn hw)).differentiableWithinAt)
    (by
      intro z
      obtain ⟨N, hz, hN⟩ := hball z
      refine ⟨ball 0 (N : ℝ), isOpen_ball.mem_nhds hz, δ, hδsum, ?_⟩
      filter_upwards [eventually_ge_atTop N] with n hn w hw
      exact hstepF n w (hN n hn hw))
  refine ⟨g, hg, ?_⟩
  intro z hz
  have H := limit_error_le_tsum
    (fun z => hconv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)) δ hδsum 0 E
    (fun n _ w hw => hstepF n w (subset_arakelianExhaustion E n hw)) z hz
  simp only [Nat.zero_add, hF0] at H
  rw [hδtotal] at H
  exact H.trans_lt (by linarith)

theorem arakelian_approximation_of_holomorphic (E : Set ℂ) (hE : IsArakelian E)
    (U : Set ℂ) (hU : IsOpen U) (hEU : E ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z ∈ E, ‖g z - f z‖ < ε :=
  arakelian_approximation E hE U hU hEU f (hf.analyticOnNhd hU) ε hε

end ComplexApproximation
