import EremenkosConjecture.StageStability
import EremenkosConjecture.EntireLimit
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The entire function obtained by successive polynomial approximation

Each step has a tolerance preserving its finite orbit and conformal-chart
conditions. Subsequent tolerances decrease geometrically. The entire limit
therefore satisfies every finite stage.
-/

open Set Metric Function Filter
open scoped Topology

namespace EremenkosConjecture
namespace UniformEscapeData

theorem exists_entire_all_stages (D : UniformEscapeData) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ ∀ n, D.StageProperty n f := by
  classical
  let p₀ : Polynomial ℂ := Polynomial.C (-3)
  have hp₀ : D.StageProperty 0 p₀.eval := by
    simpa only [p₀, Polynomial.eval_C] using D.stageProperty_initial
  obtain ⟨S₀, _, _⟩ := D.exists_approximationStage 0 p₀ hp₀ 1 zero_lt_one
  let step : (n : ℕ) → D.ApproximationStage n → D.ApproximationStage (n + 1) :=
    fun n S => (D.exists_next_approximationStage n S).choose
  let S : (n : ℕ) → D.ApproximationStage n := Nat.rec S₀ step
  let r : ℕ → ℝ := fun n => (S n).tolerance
  let F : ℕ → ℂ → ℂ := fun n => (S n).p.eval
  have hr : ∀ n, 0 < r n := fun n => (S n).positive
  have hstep (n : ℕ) : r (n + 1) ≤ r n / 2 ∧
      ∀ z ∈ controlDisc n, ‖F (n + 1) z - F n z‖ ≤ r n :=
    (D.exists_next_approximationStage n (S n)).choose_spec
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
    obtain ⟨N, hN⟩ := (controlDisc_mem_nhds_eventually z).exists
    refine ⟨controlDisc N, hN, r, hrsum, ?_⟩
    filter_upwards [eventually_ge_atTop N] with n hn w hw
    exact (hstep n).2 w (controlDisc_mono hn hw)
  obtain ⟨f, hf, hconv⟩ := exists_entire_limit_of_locally_summable_corrections F
    (fun n => (S n).p.differentiable) hlocal
  have hpoint : ∀ z, Tendsto (fun n => F n z) atTop (𝓝 (f z)) :=
    fun z => hconv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)
  refine ⟨f, hf, fun n => (S n).stable f hf ?_⟩
  intro z hz
  have H := limit_error_le_tsum hpoint r hrsum n (controlDisc n)
    (fun m hm w hw => (hstep m).2 w (controlDisc_mono hm hw)) z hz
  exact H.trans (htail n)

/-- The compact nonseparating boundary-set construction underlying Proposition 3.2. The
transcendence and dynamical boundary conclusions are separate obligations. -/
theorem exists_entire_uniform_escape_itinerary (D : UniformEscapeData) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      MapsTo f (controlDisc 0) trappingDisc ∧
      (∀ n, MapsTo (f^[n + 1]) (D.P n) trappingDisc) ∧
      (∀ n, InjOn (f^[n]) (D.K n) ∧ MapsTo (f^[n]) (D.K n) (targetDisc n)) ∧
      (∀ n, HasAmbientConformalChart (f^[n]) (D.K n)) := by
  obtain ⟨f, hf, hs⟩ := D.exists_entire_all_stages
  exact ⟨f, hf, (hs 0).1, fun n => (hs (n + 1)).2.2.2 n (Nat.lt_succ_self n),
    fun n => ⟨((hs n).2.2.1 n le_rfl).injOn, (hs n).2.1 n le_rfl⟩,
    fun n => (hs n).2.2.1 n le_rfl⟩

end UniformEscapeData
end EremenkosConjecture
