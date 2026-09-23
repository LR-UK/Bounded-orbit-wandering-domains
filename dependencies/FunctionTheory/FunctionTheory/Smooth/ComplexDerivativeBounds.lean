import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic

open Set Metric
open scoped ContDiff

namespace FunctionTheory

set_option autoImplicit false

/-- For a holomorphic germ the real Fréchet derivative norm equals the norm
of the corresponding complex derivative, in every finite order. -/
theorem norm_real_iteratedFDeriv_eq_complex_iteratedDeriv
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) (n : ℕ) :
    ‖iteratedFDeriv ℝ n f a‖ = ‖iteratedDeriv n f a‖ := by
  have hC : ContDiffAt ℂ (n : ℕ∞ω) f a := hf.contDiffAt
  rw [← hC.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv]

/-- Cauchy's bound stated in the real derivative norms used for smooth
extensions of planar holomorphic maps. -/
theorem norm_real_iteratedFDeriv_le_of_circle_bound
    (n : ℕ) {f : ℂ → ℂ} {a : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall a R))
    (hbound : ∀ z ∈ sphere a R, ‖f z‖ ≤ M) :
    ‖iteratedFDeriv ℝ n f a‖ ≤ n.factorial * M / R ^ n := by
  rw [norm_real_iteratedFDeriv_eq_complex_iteratedDeriv (hf a (mem_closedBall_self hR.le))]
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR _ hbound
  refine ⟨hf.differentiableOn.mono ball_subset_closedBall, ?_⟩
  simpa only [closure_ball a hR.ne'] using hf.continuousOn

/-- Uniform holomorphic error on an open neighbourhood controls all real
derivatives up to any prescribed finite order on a compact subset. -/
theorem exists_uniform_real_derivative_bound_on_compact
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (m : ℕ) :
    ∃ M > 0, ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f U →
      ∀ δ ≥ 0, (∀ z ∈ U, ‖f z‖ ≤ δ) →
      ∀ n ≤ m, ∀ z ∈ K, ‖iteratedFDeriv ℝ n f z‖ ≤ M * δ := by
  obtain ⟨R, hR, Htube⟩ := hK.exists_thickening_subset_open hU hKU
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have Hball : ∀ a ∈ K, closedBall a r ⊆ U := by
    intro a ha z hz
    exact Htube (mem_thickening_iff.mpr ⟨a, ha,
      (mem_closedBall.mp hz).trans_lt (half_lt_self hR)⟩)
  let b : ℕ → ℝ := fun n => (n.factorial : ℝ) / r ^ n
  have hb : ∀ n, 0 ≤ b n := fun n => div_nonneg (by positivity) (pow_nonneg hr.le n)
  let M : ℝ := 1 + ∑ i ∈ Finset.range (m + 1), b i
  have hM : 0 < M := by
    have hsum := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range (m + 1)) => hb i)
    dsimp [M]
    linarith
  have hbM : ∀ n ≤ m, b n ≤ M := by
    intro n hn
    have hle := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (m + 1)) => hb i)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
    dsimp [M]
    linarith
  refine ⟨M, hM, ?_⟩
  intro f hf δ hδ hbound n hn z hz
  calc
    ‖iteratedFDeriv ℝ n f z‖ ≤ n.factorial * δ / r ^ n :=
      norm_real_iteratedFDeriv_le_of_circle_bound n hr (hf.mono (Hball z hz))
        (fun w hw => hbound w (Hball z hz (sphere_subset_closedBall hw)))
    _ = b n * δ := by dsimp [b]; ring
    _ ≤ M * δ := mul_le_mul_of_nonneg_right (hbM n hn) hδ

end FunctionTheory
