import EremenkosConjecture.VariableStageStability
import EremenkosConjecture.EntireLimit
import Mathlib.Analysis.SpecificLimits.Basic

/-! # The entire limit with adaptively chosen control radii -/

open Set Metric Function Filter
open scoped Topology

namespace EremenkosConjecture.VariableConstruction

structure ApproximationChain (D : UniformEscapeData) where
  stage : (n : ℕ) → ApproximationStage D n
  next : ∀ n, IsNext (stage n) (stage (n + 1))

namespace ApproximationChain

variable {D : UniformEscapeData} (C : ApproximationChain D)

def radius (n : ℕ) : ℝ := (C.stage n).schedule.radius n
def center (n : ℕ) : ℝ := (C.stage n).schedule.center n
def control (n : ℕ) : Set ℂ := variableControlDisc (C.radius n)
def target (n : ℕ) : Set ℂ := variableTargetDisc (C.center n)

theorem radius_coherent {j n : ℕ} (hjn : j ≤ n) :
    (C.stage n).schedule.radius j = C.radius j := by
  induction n, hjn using Nat.le_induction with
  | base => rfl
  | succ n hn ih => exact ((C.next n).1 j hn).trans ih

theorem center_coherent {j n : ℕ} (hjn : j ≤ n) :
    (C.stage n).schedule.center j = C.center j := by
  simp only [DiscSchedule.center, C.radius_coherent hjn, center, radius]

theorem radius_lower (n : ℕ) : 1 + 5 * n ≤ C.radius n :=
  (C.stage n).schedule.radius_lower le_rfl

theorem center_lower (n : ℕ) : 5 * n ≤ C.center n := by
  by_cases hn : n = 0
  · subst n; simp [center, DiscSchedule.center]
  · have H := C.radius_lower n
    simp only [center, DiscSchedule.center, ite_eq_right hn]
    change 5 * n ≤ C.radius n
    linarith

theorem control_mono : Monotone C.control := by
  intro n m hnm
  have H := (C.stage m).schedule.control_mono hnm le_rfl
  rw [C.radius_coherent hnm] at H
  exact H

theorem control_mem_nhds_eventually (z : ℂ) :
    ∀ᶠ n : ℕ in atTop, C.control n ∈ 𝓝 z := by
  obtain ⟨N, hN⟩ := exists_nat_gt (dist z (-3))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have H := C.radius_lower n
  have hz : z ∈ ball (-3 : ℂ) (C.radius n) := by
    change dist z (-3) < _
    linarith
  exact Filter.mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall

theorem target_subset_next_control (n : ℕ) : C.target n ⊆ C.control (n + 1) := by
  have H := (C.stage (n + 1)).schedule.target_subset_control_interior
    (Nat.lt_succ_self n) le_rfl
  rw [C.center_coherent (Nat.le_succ n)] at H
  exact H.trans interior_subset

theorem disjoint_targets {n m : ℕ} (hnm : n ≠ m) : Disjoint (C.target n) (C.target m) := by
  have H := (C.stage (max n m)).schedule.disjoint_targets
    (le_max_left n m) (le_max_right n m) hnm
  rw [C.center_coherent (le_max_left n m), C.center_coherent (le_max_right n m)] at H
  exact H

theorem uniformEscape (f : ℂ → ℂ) (K : Set ℂ)
    (hmap : ∀ n, MapsTo (f^[n]) K (C.target n)) : ComplexDynamics.EscapesUniformlyOn f K := by
  intro R
  obtain ⟨N, hN⟩ := exists_nat_gt (R + 1)
  filter_upwards [eventually_ge_atTop N] with n hn z hz
  have h := (variableTargetDisc_re_bounds (hmap n hz)).1
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hc := C.center_lower n
  have hre := (le_abs_self ((f^[n]) z).re).trans (Complex.abs_re_le_norm _)
  linarith

end ApproximationChain

structure EntireConstruction (D : UniformEscapeData) where
  chain : ApproximationChain D
  f : ℂ → ℂ
  entire : Differentiable ℂ f
  close : ∀ n, ∀ z ∈ chain.control n,
    ‖f z - (chain.stage n).p.eval z‖ ≤ 2 * (chain.stage n).tolerance
  property : ∀ n, StageProperty D (chain.stage n).schedule f

theorem exists_entireConstruction (D : UniformEscapeData) : Nonempty (EntireConstruction D) := by
  classical
  let p₀ : Polynomial ℂ := Polynomial.C (-3)
  have hp₀ : StageProperty D DiscSchedule.initialSchedule p₀.eval := by
    simpa only [p₀, Polynomial.eval_C] using stageProperty_initial D
  obtain ⟨S₀, _, _, _⟩ := exists_approximationStage D DiscSchedule.initialSchedule p₀ hp₀ 1 zero_lt_one
  let step : (n : ℕ) → ApproximationStage D n → ApproximationStage D (n + 1) :=
    fun _ S => (exists_next_approximationStage D S).choose
  let S : (n : ℕ) → ApproximationStage D n := Nat.rec S₀ step
  let C : ApproximationChain D := ⟨S, fun n => (exists_next_approximationStage D (S n)).choose_spec⟩
  let r : ℕ → ℝ := fun n => (S n).tolerance
  let F : ℕ → ℂ → ℂ := fun n => (S n).p.eval
  have hr : ∀ n, 0 < r n := fun n => (S n).positive
  have hstep (n : ℕ) : r (n + 1) ≤ r n / 2 ∧
      ∀ z ∈ C.control n, ‖F (n + 1) z - F n z‖ ≤ r n :=
    ⟨(C.next n).2.1, (C.next n).2.2.1⟩
  have hgeom (k m : ℕ) : r (k + m) ≤ r k * (1 / 2 : ℝ) ^ m := by
    have H := le_geom (u := fun i => r (k + i)) (c := 1 / 2) (by norm_num) m
      (fun i _ => by
        have h := (hstep (k + i)).1
        simpa only [Nat.add_assoc, div_eq_mul_inv, one_mul, mul_comm] using h)
    simpa only [Nat.add_zero, mul_comm] using H
  have hrsum : Summable r := Summable.of_nonneg_of_le (fun n => (hr n).le)
    (fun n => by simpa only [Nat.zero_add] using hgeom 0 n)
    (summable_geometric_two.mul_left (r 0))
  have htail (k : ℕ) : (∑' m, r (k + m)) ≤ 2 * r k := by
    have hshift : Summable (fun m => r (k + m)) := hrsum.comp_injective (add_right_injective k)
    calc
      (∑' m, r (k + m)) ≤ ∑' m, r k * (1 / 2 : ℝ) ^ m :=
        Summable.tsum_le_tsum (hgeom k) hshift (summable_geometric_two.mul_left (r k))
      _ = 2 * r k := by rw [tsum_mul_left, tsum_geometric_two]; ring
  have hlocal : ∀ z : ℂ, ∃ A ∈ 𝓝 z, ∃ ε : ℕ → ℝ, Summable ε ∧
      ∀ᶠ n : ℕ in atTop, ∀ w ∈ A, ‖F (n + 1) w - F n w‖ ≤ ε n := by
    intro z
    obtain ⟨N, hN⟩ := (C.control_mem_nhds_eventually z).exists
    refine ⟨C.control N, hN, r, hrsum, ?_⟩
    filter_upwards [eventually_ge_atTop N] with n hn w hw
    exact (hstep n).2 w (C.control_mono hn hw)
  obtain ⟨f, hf, hconv⟩ := exists_entire_limit_of_locally_summable_corrections F
    (fun n => (S n).p.differentiable) hlocal
  have hpoint : ∀ z, Tendsto (fun n => F n z) atTop (𝓝 (f z)) :=
    fun z => hconv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)
  have hclose (n : ℕ) : ∀ z ∈ C.control n, ‖f z - F n z‖ ≤ 2 * r n := by
    intro z hz
    have H := limit_error_le_tsum hpoint r hrsum n (C.control n)
      (fun m hm w hw => (hstep m).2 w (C.control_mono hm hw)) z hz
    exact H.trans (htail n)
  exact ⟨⟨C, f, hf, hclose, fun n => (S n).stable f hf (hclose n)⟩⟩

end EremenkosConjecture.VariableConstruction
