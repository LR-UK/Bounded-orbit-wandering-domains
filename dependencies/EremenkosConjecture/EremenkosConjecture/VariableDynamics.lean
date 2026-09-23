import EremenkosConjecture.VariableEntireLimit
import ComplexDynamics.Transcendence
import ComplexDynamics.UniformEscape

/-! # Fast escape and transcendence of the variable-disk construction -/

open Set Metric Function Filter ComplexDynamics
open scoped Topology

namespace EremenkosConjecture.VariableConstruction.EntireConstruction

variable {D : UniformEscapeData} (W : EntireConstruction D)

theorem maps_target (n : ℕ) : MapsTo (W.f^[n]) (D.K n) (W.chain.target n) :=
  (W.property n).2.1 n le_rfl

theorem charts (n : ℕ) : HasAmbientConformalChart (W.f^[n]) (D.K n) :=
  (W.property n).2.2.1 n le_rfl

theorem maps_points (n : ℕ) : MapsTo (W.f^[n + 1]) (D.P n) trappingDisc :=
  (W.property (n + 1)).2.2.2 n (Nat.lt_succ_self n)

theorem maximum_step {n : ℕ} (hn : 0 < n) :
    maximumModulus W.f (W.chain.radius n - 3) ≤ W.chain.radius (n + 1) - 3 := by
  have hr := W.chain.radius_lower n
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have herr : ∀ z ∈ closedBall 0 (W.chain.radius n - 3),
      ‖W.f z - (W.chain.stage n).p.eval z‖ ≤ 1 := by
    intro z hz
    have hdist := dist_triangle z (0 : ℂ) (-3)
    have hz' : dist z 0 ≤ W.chain.radius n - 3 := hz
    rw [show dist (0 : ℂ) (-3) = 3 by norm_num] at hdist
    have hc : z ∈ W.chain.control n := by
      change dist z (-3 : ℂ) ≤ W.chain.radius n
      linarith
    have H := W.close n z hc
    have Hsmall := (W.chain.stage n).small
    linarith
  have H := maximumModulus_le_of_uniform_error (W.chain.stage n).p.continuous
    (by linarith : 0 ≤ W.chain.radius n - 3) herr
  have Hnext := (W.chain.next n).2.2.2.2
  change maximumModulus (W.chain.stage n).p.eval (W.chain.radius n - 3) + 2 <
    W.chain.radius (n + 1) - 3 at Hnext
  linarith

theorem orbit_lower {K : Set ℂ} (hK : ∀ n, K ⊆ D.K n) {z : ℂ} (hz : z ∈ K)
    {n : ℕ} (hn : 0 < n) : W.chain.radius n - 3 ≤ ‖(W.f^[n]) z‖ := by
  have H := (variableTargetDisc_re_bounds (W.maps_target n (hK n hz))).1
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have Hcenter : W.chain.center n = W.chain.radius n := by
    simp [ApproximationChain.center, ApproximationChain.radius, DiscSchedule.center, hn0]
  change W.chain.center n - 1 < ((W.f^[n]) z).re at H
  rw [Hcenter] at H
  have Hre := (le_abs_self ((W.f^[n]) z).re).trans (Complex.abs_re_le_norm _)
  linarith

theorem escapesUniformly {K : Set ℂ} (hK : ∀ n, K ⊆ D.K n) :
    EscapesUniformlyOn W.f K := W.chain.uniformEscape W.f K
      (fun n _ hz => W.maps_target n (hK n hz))

theorem fastEscapeAtRadius {K : Set ℂ} (hK : ∀ n, K ⊆ D.K n) :
    K ⊆ fastEscapingSetAtRadius W.f (W.chain.radius 1 - 3) := by
  intro z hz
  apply mem_fastEscapingSetAtRadius_of_radius_sequence W.entire.continuous
    ((W.escapesUniformly hK).subset_escapingSet hz) (fun n => W.chain.radius (n + 1) - 3)
    (fun n => ?_) (fun n => W.maximum_step (Nat.succ_pos n)) 1
    (fun n => W.orbit_lower hK hz (Nat.succ_pos n))
  have H := W.chain.radius_lower (n + 1)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  push_cast at H
  linarith

theorem bounded_boundary_values (n : ℕ) {q : ℂ}
    (hq : q ∈ ((W.chain.stage n).p.eval^[n]) '' D.P n) : ‖W.f q‖ ≤ 4 := by
  have htarget : q ∈ W.chain.target n := by
    obtain ⟨z, hz, rfl⟩ := hq
    exact (W.chain.stage n).property.2.1 n le_rfl (D.points_subset n hz)
  have hcontrol := W.chain.target_subset_next_control n htarget
  have He := W.close (n + 1) q hcontrol
  have Hq := (W.chain.next n).2.2.2.1 q hq
  have Htol := (W.chain.next n).2.1
  have Hsmall := (W.chain.stage n).small
  have H := norm_le_norm_add_norm_sub ((W.chain.stage (n + 1)).p.eval q) (W.f q)
  have H' := norm_le_norm_add_norm_sub (-3 : ℂ) ((W.chain.stage (n + 1)).p.eval q)
  rw [norm_sub_rev] at H H'
  rw [show ‖(-3 : ℂ)‖ = (3 : ℝ) by norm_num] at H'
  linarith

/-- The construction works at every nonnegative starting radius. Thus its
fast-escape conclusion does not require a general radius-independence theorem. -/
theorem fastEscapeAtEveryRadius {K : Set ℂ} (hK : ∀ n, K ⊆ D.K n)
    (r : ℝ) (hr : 0 ≤ r) : K ⊆ fastEscapingSetAtRadius W.f r := by
  obtain ⟨N, hN⟩ := exists_nat_gt (r + 3)
  let l := N + 1
  have hl : 0 < l := Nat.succ_pos N
  have hstart : r ≤ W.chain.radius l - 3 := by
    have H := W.chain.radius_lower l
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
    dsimp [l] at H
    push_cast at H
    linarith
  have hcompare (n : ℕ) : 0 ≤ ((maximumModulus W.f)^[n]) r ∧
      ((maximumModulus W.f)^[n]) r ≤ W.chain.radius (n + l) - 3 := by
    induction n with
    | zero => simpa only [iterate_zero_apply, Nat.zero_add] using And.intro hr hstart
    | succ n ih =>
      rw [iterate_succ_apply']
      refine ⟨maximumModulus_nonneg W.entire.continuous ih.1, ?_⟩
      have H := (maximumModulus_mono W.entire.continuous ih.1 ih.2).trans
        (W.maximum_step (by omega : 0 < n + l))
      simpa only [Nat.succ_add] using H
  intro z hz
  exact ⟨(W.escapesUniformly hK).subset_escapingSet hz, l,
    fun n => (hcompare n).2.trans (W.orbit_lower hK hz (by omega))⟩

theorem transcendental {K : Set ℂ} (hK : ∀ n, K ⊆ D.K n)
    (hne : K.Nonempty) (hP : ∀ n, (D.P n).Nonempty) : IsTranscendentalEntire W.f := by
  classical
  choose z hz using hP
  let q : ℕ → ℂ := fun n => ((W.chain.stage n).p.eval^[n]) (z n)
  have hq (n : ℕ) : q n ∈ W.chain.target n :=
    (W.chain.stage n).property.2.1 n le_rfl (D.points_subset n (hz n))
  have htend : Tendsto (fun n => ‖q n‖) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro R
    obtain ⟨N, hN⟩ := exists_nat_gt (R + 1)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have H := (variableTargetDisc_re_bounds (hq n)).1
    have Hcenter := W.chain.center_lower n
    have Hre := (le_abs_self (q n).re).trans (Complex.abs_re_le_norm _)
    linarith
  obtain ⟨w, hw⟩ := hne
  exact isTranscendentalEntire_of_escape_and_bounded_values W.entire
    ((W.escapesUniformly hK).subset_escapingSet hw) q htend 4
    (fun n => W.bounded_boundary_values n (mem_image_of_mem _ (hz n)))

end EremenkosConjecture.VariableConstruction.EntireConstruction
