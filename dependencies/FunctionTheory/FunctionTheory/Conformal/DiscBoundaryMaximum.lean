import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

open Set Metric Filter
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- A uniform boundary limsup bounds a holomorphic function throughout the
open disc. No boundary values or continuous extension are assumed. -/
theorem norm_le_of_disc_boundary_limsup
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball (0:ℂ) 1)) {C : ℝ}
    (hbound : ∀ ε : ℝ, 0<ε → ∃ r : ℝ, r<1 ∧
      ∀ z∈ball (0:ℂ) 1, r<‖z‖ → ‖f z‖≤C+ε) :
    ∀ z∈ball (0:ℂ) 1, ‖f z‖≤C := by
  intro z hz
  by_contra hnot
  have hpos : 0<(‖f z‖-C)/2 := by linarith
  obtain ⟨r,hr,hB⟩ := hbound ((‖f z‖-C)/2) hpos
  let M := max ‖z‖ r
  let R := (M+1)/2
  have hM : M<1 := max_lt (mem_ball_zero_iff.mp hz) hr
  have hM0 : 0≤M := le_trans (norm_nonneg z) (le_max_left _ _)
  have hR0 : 0<R := by dsimp [R]; linarith
  have hR1 : R<1 := by dsimp [R]; linarith
  have hMR : M<R := by dsimp [R]; linarith
  have hrR : r<R := (le_max_right _ _).trans_lt hMR
  have hzR : ‖z‖<R := (le_max_left _ _).trans_lt hMR
  have hK : closedBall (0:ℂ) R⊆ball (0:ℂ) 1 := closedBall_subset_ball hR1
  have H : ‖f z‖≤C+(‖f z‖-C)/2 := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      ((hf.mono hK).differentiableOn.diffContOnCl_ball subset_rfl)
    · intro w hw
      have hwR : ‖w‖=R := by
        simpa only [sub_zero] using mem_sphere_iff_norm.mp (frontier_ball_subset_sphere hw)
      exact hB w (mem_ball_zero_iff.mpr (hwR.symm ▸ hR1)) (hwR.symm ▸ hrR)
    · rw [closure_ball _ hR0.ne']
      exact mem_closedBall_zero_iff.mpr hzR.le
  linarith

/-- If both a nonvanishing holomorphic function and its reciprocal have
boundary limsup at most one, the function is a unimodular constant. -/
theorem eq_unimodular_const_of_disc_boundary_bounds
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball (0:ℂ) 1))
    (hne : ∀ z∈ball (0:ℂ) 1, f z≠0)
    (hupper : ∀ ε : ℝ, 0<ε → ∃ r : ℝ, r<1 ∧
      ∀ z∈ball (0:ℂ) 1, r<‖z‖ → ‖f z‖≤1+ε)
    (hlower : ∀ ε : ℝ, 0<ε → ∃ r : ℝ, r<1 ∧
      ∀ z∈ball (0:ℂ) 1, r<‖z‖ → ‖(f z)⁻¹‖≤1+ε) :
    ∃ c : ℂ, ‖c‖=1 ∧ EqOn f (fun _ => c) (ball (0:ℂ) 1) := by
  have hu := norm_le_of_disc_boundary_limsup hf hupper
  have hInv : AnalyticOnNhd ℂ (fun z => (f z)⁻¹) (ball (0:ℂ) 1) :=
    fun z hz => (hf z hz).inv (hne z hz)
  have hl := norm_le_of_disc_boundary_limsup hInv hlower
  have hnorm : ∀ z∈ball (0:ℂ) 1, ‖f z‖=1 := by
    intro z hz
    apply le_antisymm (hu z hz)
    have H := mul_le_mul_of_nonneg_left (hl z hz) (norm_nonneg (f z))
    simpa only [norm_inv,mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hne z hz)),mul_one] using H
  refine ⟨f 0,hnorm 0 (mem_ball_self one_pos),?_⟩
  apply Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
    (convex_ball (0:ℂ) 1).isPreconnected isOpen_ball hf.differentiableOn (mem_ball_self one_pos)
  intro z hz
  change ‖f z‖≤‖f 0‖
  rw [hnorm z hz,hnorm 0 (mem_ball_self one_pos)]

end FunctionTheory
