import EremenkosConjecture.RaySuccessor
import EremenkosConjecture.EntireLimit

/-! # The entire limit of the ray construction -/

open Set Metric Function Filter
open scoped Topology

namespace EremenkosConjecture

open Scaffolding

structure RayChain where
  stage : (n : ℕ) → RayStage n
  step : ∀ n, RayStep (stage n) (stage (n + 1))

theorem exists_rayChain : Nonempty RayChain := by
  classical
  obtain ⟨S₀⟩ := exists_initial_rayStage
  let step : (n : ℕ) → RayStage n → RayStage (n + 1) :=
    fun _ S => (exists_next_rayStage S).choose
  let S : (n : ℕ) → RayStage n := Nat.rec S₀ step
  exact ⟨⟨S, fun n => (exists_next_rayStage (S n)).choose_spec⟩⟩

theorem tendsto_zero_of_halving {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n)
    (hstep : ∀ n, u (n + 1) ≤ u n / 2) : Tendsto u atTop (𝓝 0) := by
  have hgeom (n : ℕ) : u n ≤ u 0 * (1 / 2 : ℝ) ^ n := by
    have h := le_geom (u := u) (c := 1 / 2) (by norm_num) n
      (fun k _ => by simpa only [div_eq_mul_inv, one_mul, mul_comm] using hstep k)
    simpa only [mul_comm] using h
  have ht : Tendsto (fun n : ℕ => u 0 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (u 0)
  exact squeeze_zero hu hgeom ht

structure RayEntireConstruction where
  chain : RayChain
  f : ℂ → ℂ
  entire : Differentiable ℂ f
  close : ∀ n, ∀ z ∈ background n, dist (f z) ((chain.stage n).f z) ≤ (chain.stage n).reserve / 2
  property : ∀ n, RayOrbitProperty n (chain.stage n).a (chain.stage n).b f

theorem exists_rayEntireConstruction : Nonempty RayEntireConstruction := by
  obtain ⟨C⟩ := exists_rayChain
  let r : ℕ → ℝ := fun n => (C.stage n).reserve / 4
  let F : ℕ → ℂ → ℂ := fun n => (C.stage n).f
  have hr : ∀ n, 0 < r n := fun n => div_pos (C.stage n).reserve_pos (by norm_num)
  have hstep (n : ℕ) : r (n + 1) ≤ r n / 2 ∧
      ∀ z ∈ background n, ‖F (n + 1) z - F n z‖ ≤ r n := by
    constructor
    · have h := (C.step n).reserve
      dsimp [r]
      linarith
    · intro z hz
      simpa only [dist_eq_norm] using (C.step n).correction z hz
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
    obtain ⟨N, hN⟩ := background_exhausts_closedBalls (‖z‖ + 1)
    have hA : closedBall (0 : ℂ) (‖z‖ + 1) ∈ 𝓝 z := by
      apply Filter.mem_of_superset (isOpen_ball.mem_nhds ?_) ball_subset_closedBall
      simpa only [mem_ball, dist_zero_right] using lt_add_one ‖z‖
    refine ⟨closedBall 0 (‖z‖ + 1), hA, r, hrsum, ?_⟩
    filter_upwards [eventually_ge_atTop N] with n hn w hw
    exact (hstep n).2 w (hN n hn hw)
  obtain ⟨f, hf, hconv⟩ := exists_entire_limit_of_locally_summable_corrections F
    (fun n => (C.stage n).entire) hlocal
  have hpoint : ∀ z, Tendsto (fun n => F n z) atTop (𝓝 (f z)) :=
    fun z => hconv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)
  have hclose (n : ℕ) : ∀ z ∈ background n, dist (f z) (F n z) ≤ (C.stage n).reserve / 2 := by
    intro z hz
    have H := limit_error_le_tsum hpoint r hrsum n (background n)
      (fun m hm w hw => (hstep m).2 w (background_monotone hm hw)) z hz
    have h := H.trans (htail n)
    rw [dist_eq_norm]
    dsimp [r] at h
    linarith
  refine ⟨⟨C, f, hf, hclose, fun n => (C.step n).stable f ?_⟩⟩
  intro z hz
  exact (hclose (n + 1) z hz).trans_lt (half_lt_self (C.stage (n + 1)).reserve_pos)

namespace RayEntireConstruction

theorem widths_tendsto (C : RayEntireConstruction) :
    Tendsto (fun n => (C.chain.stage n).a) atTop (𝓝 0) ∧
      Tendsto (fun n => (C.chain.stage n).b) atTop (𝓝 0) :=
  ⟨tendsto_zero_of_halving (fun n => (C.chain.stage n).a_pos.le) (fun n => (C.chain.step n).width),
    tendsto_zero_of_halving (fun n => (C.chain.stage n).b_pos.le) (fun n => (C.chain.step n).height)⟩

theorem trapping (C : RayEntireConstruction) : MapsTo C.f trappingDisk (ball 0 (1 / 2)) := by
  intro z hz
  have hc := C.close 0 z (trappingDisk_subset_background 0 hz)
  rw [dist_eq_norm] at hc
  have ht := norm_le_norm_sub_add (C.f z) ((C.chain.stage 0).f z)
  have hs := (C.chain.stage 0).trapping z hz
  have hr := (C.chain.stage 0).reserve_pos
  exact mem_ball_zero_iff.mpr (by linarith)

end RayEntireConstruction

end EremenkosConjecture
