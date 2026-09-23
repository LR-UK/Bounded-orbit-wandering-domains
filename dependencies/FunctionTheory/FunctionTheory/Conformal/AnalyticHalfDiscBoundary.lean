import FunctionTheory.Topology.LocalHomeomorphBoundary
import FunctionTheory.Conformal.CircularArcCap
import Mathlib.Analysis.Complex.Convex

open Set Metric Complex Filter
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- The part of a closed half-disc's boundary that belongs to a domain
avoiding its diameter is precisely on the open semicircle. The formulation
is transported through an arbitrary local homeomorphism. -/
theorem exists_arc_parameter_of_frontier_half_disc_image
    (e : OpenPartialHomeomorph ℂ ℂ) {U : Set ℂ} {ρ : ℝ} (hρ : 0<ρ)
    (hKt : closedBall (0:ℂ) ρ∩{w : ℂ | 0≤w.re}⊆e.target)
    (hline : ∀ w∈closedBall (0:ℂ) ρ, w.re=0 → e.symm w∉U)
    {z : ℂ} (hz : z∈frontier (e.symm '' (closedBall (0:ℂ) ρ∩{w : ℂ | 0≤w.re}))∩U) :
    ∃ θ∈Ioo (-(Real.pi/2)) (Real.pi/2), z=e.symm (circleMap 0 ρ θ) := by
  let K := closedBall (0:ℂ) ρ∩{w : ℂ | 0≤w.re}
  have hK : IsCompact K := (isCompact_closedBall (0:ℂ) ρ).inter_right
    (isClosed_le continuous_const Complex.continuous_re)
  have hft : e.symm '' frontier K=frontier (e.symm '' K) :=
    image_frontier_of_compact_closure e.symm (by rwa [hK.isClosed.closure_eq])
      (by rwa [hK.isClosed.closure_eq])
  have hzft := hz.1
  change z∈frontier (e.symm '' K) at hzft
  rw [← hft] at hzft
  obtain ⟨w,hw,rfl⟩ := hzft
  have hwK : w∈K := hK.isClosed.frontier_subset hw
  have hre : 0<w.re := by
    have H : 0≤w.re := hwK.2
    by_contra hn
    have heq : w.re=0 := le_antisymm (le_of_not_gt hn) H
    exact hline w hwK.1 heq hz.2
  have hnorm : ‖w‖=ρ := by
    apply le_antisymm (mem_closedBall_zero_iff.mp hwK.1)
    by_contra hn
    have hwball : w∈ball (0:ℂ) ρ := mem_ball_zero_iff.mpr (lt_of_not_ge hn)
    have hopen : IsOpen (ball (0:ℂ) ρ∩{v : ℂ | 0<v.re}) :=
      isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
    have hsub : ball (0:ℂ) ρ∩{v : ℂ | 0<v.re}⊆K :=
      fun v hv => ⟨ball_subset_closedBall hv.1,(show 0<v.re from hv.2).le⟩
    have hint : w∈interior K := interior_mono hsub (hopen.interior_eq.symm ▸ ⟨hwball,hre⟩)
    exact hw.2 hint
  have harg : |w.arg|<Real.pi/2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  refine ⟨w.arg,abs_lt.mp harg,?_⟩
  congr 1
  simpa only [circleMap_zero,← hnorm] using (norm_mul_exp_arg_mul_I w).symm

end FunctionTheory
