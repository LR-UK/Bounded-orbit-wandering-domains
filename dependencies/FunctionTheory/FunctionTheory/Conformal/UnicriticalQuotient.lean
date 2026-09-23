import FunctionTheory.Conformal.DiscBoundaryMaximum
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Set Metric Filter
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- Strict positivity of the real part on the circle holds throughout the
closed disc. This is the maximum principle applied to `exp (-f)`. -/
theorem re_pos_on_closedDisc_of_re_pos_on_circle
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall (0:ℂ) 1))
    (hcircle : ∀ z : ℂ, ‖z‖=1 → 0<(f z).re) :
    ∀ z∈closedBall (0:ℂ) 1, 0<(f z).re := by
  let e : ℂ → ℂ := fun z => Complex.exp (-f z)
  have he : AnalyticOnNhd ℂ e (closedBall (0:ℂ) 1) := hf.neg.cexp
  obtain ⟨a,ha,hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm isBounded_ball
    (nonempty_ball.mpr (by norm_num : (0:ℝ)<1))
    (he.differentiableOn.diffContOnCl_ball subset_rfl)
  have ha1 : ‖a‖=1 := by
    simpa only [sub_zero] using mem_sphere_iff_norm.mp (frontier_ball_subset_sphere ha)
  have hEa : ‖e a‖<1 := by
    dsimp only [e]
    rw [Complex.norm_exp,Complex.neg_re,Real.exp_lt_one_iff]
    linarith [hcircle a ha1]
  intro z hz
  have hzcl : z∈closure (ball (0:ℂ) 1) := by rw [closure_ball _ one_ne_zero]; exact hz
  have H : ‖e z‖<1 := (hmax hzcl).trans_lt hEa
  dsimp only [e] at H
  rw [Complex.norm_exp,Complex.neg_re,Real.exp_lt_one_iff] at H
  linarith

/-- At a zero of finite order, the quotient `f/(z*f')` has a removable
singularity at zero. If there are no other critical points in the closed
disc, it admits a holomorphic representative on the whole closed disc. -/
theorem exists_analytic_quotient_by_mul_deriv
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall (0:ℂ) 1))
    (hf0 : f 0=0) (ho : meromorphicOrderAt f 0≠⊤)
    (hcrit : ∀ z∈closedBall (0:ℂ) 1, z≠0 → deriv f z≠0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall (0:ℂ) 1) ∧
      ∀ z∈closedBall (0:ℂ) 1, z≠0 → g z=f z/(z*deriv f z) := by
  let H : ℂ → ℂ := fun z => f z/(z*deriv f z)
  have hH : MeromorphicOn H (closedBall (0:ℂ) 1) := by
    intro z hz
    exact (hf z hz).meromorphicAt.div (analyticAt_id.mul (hf z hz).deriv).meromorphicAt
  have hHa : ∀ z∈closedBall (0:ℂ) 1, z≠0 → AnalyticAt ℂ H z := by
    intro z hz hn
    exact (hf z hz).div (analyticAt_id.mul (hf z hz).deriv)
      (mul_ne_zero hn (hcrit z hz hn))
  have hH0 : meromorphicOrderAt H 0=0 := by
    have h0 := hf 0 (mem_closedBall_self zero_le_one)
    lift meromorphicOrderAt f 0 to ℤ using ho with k hk
    have hk0 : k≠0 := by
      intro Hk
      have Hord : meromorphicOrderAt f 0=0 := by rw [← hk,Hk]; rfl
      exact (h0.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp Hord) hf0
    have hderiv := meromorphicOrderAt_deriv_eq_sub_one (Int.cast_ne_zero.mpr hk0 : (k:ℂ)≠0) hk.symm
    have hden : meromorphicOrderAt ((id : ℂ → ℂ)*deriv f) 0=(k:WithTop ℤ) := by
      change meromorphicOrderAt ((id : ℂ → ℂ)*deriv f) 0=(k:WithTop ℤ)
      rw [meromorphicOrderAt_mul analyticAt_id.meromorphicAt h0.deriv.meromorphicAt]
      change meromorphicOrderAt (id : ℂ → ℂ) 0+meromorphicOrderAt (deriv f) 0=(k:WithTop ℤ)
      rw [meromorphicOrderAt_id,hderiv]
      norm_cast
      ring
    change meromorphicOrderAt (f / ((id : ℂ → ℂ)*deriv f)) 0=0
    rw [meromorphicOrderAt_div h0.meromorphicAt (analyticAt_id.mul h0.deriv).meromorphicAt,
      hden,← hk]
    simp
  let g := toMeromorphicNFOn H (closedBall (0:ℂ) 1)
  refine ⟨g,?_,?_⟩
  · intro z hz
    apply (meromorphicNFOn_toMeromorphicNFOn H (closedBall (0:ℂ) 1) hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hH hz]
    by_cases hn : z=0
    · rw [hn,hH0]
    · exact (hHa z hz hn).meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr (hHa z hz hn)
  · intro z hz hn
    change toMeromorphicNFOn H (closedBall (0:ℂ) 1) z=H z
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hH hz,
      toMeromorphicNFAt_eq_self.mpr (hHa z hz hn).meromorphicNFAt]

end FunctionTheory
