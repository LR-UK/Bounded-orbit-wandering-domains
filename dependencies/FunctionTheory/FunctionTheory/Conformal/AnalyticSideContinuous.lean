import FunctionTheory.Conformal.AnalyticSideLimit
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

open Set Metric Complex Filter Function
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- A conformal disc map extends continuously along a chosen side of a
local analytic boundary coordinate, even if the domain occupies both
sides of the arc. The other parts of the boundary are unrestricted. -/
theorem exists_continuous_extension_at_analytic_side
    {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (e : OpenPartialHomeomorph ℂ ℂ) (hei : DifferentiableOn ℂ e.symm e.target)
    {R : ℝ} (hR : 0<R) (hT : closedBall (0:ℂ) R⊆e.target)
    (hhalf : ∀ z∈ball (0:ℂ) R, 0<z.re → e.symm z∈U)
    (hline : ∀ z∈ball (0:ℂ) R, z.re=0 → e.symm z∉U) :
    ∃ F : ℂ → ℂ,
      ContinuousOn F (ball 0 (R/2)∩{z : ℂ | 0≤z.re}) ∧
      EqOn F (fun z => f (e.symm z)) (ball 0 (R/2)∩{z : ℂ | 0<z.re}) ∧
      ∀ z∈ball (0:ℂ) (R/2), z.re=0 → F z∈sphere (0:ℂ) 1 := by
  let W := ball (0:ℂ) R∩{z : ℂ | 0<z.re}
  let B := ball (0:ℂ) (R/2)∩{z : ℂ | 0≤z.re}
  let H : ℂ → ℂ := fun z => f (e.symm z)
  have hWT : W⊆e.target := fun z hz => hT (ball_subset_closedBall hz.1)
  have hWU : MapsTo e.symm W U := fun z hz => hhalf z hz.1 hz.2
  have hHd : DifferentiableOn ℂ H W := hf.comp (hei.mono hWT) hWU
  have hBW : B⊆closure W := by
    intro z hz
    exact mem_closure_right_half_ball ((mem_ball_zero_iff.mp hz.1).trans (half_lt_self hR)) hz.2
  have hlim (c : ℂ) (hc : c∈ball (0:ℂ) (R/2)) (hc0 : c.re=0) :
      ∃ a∈sphere (0:ℂ) 1, Tendsto H (𝓝[W] c) (𝓝 a) := by
    let E := e.transHomeomorph (Homeomorph.addRight c).symm
    have hEi : DifferentiableOn ℂ E.symm E.target := by
      change DifferentiableOn ℂ (fun z => e.symm (z+c)) ((fun z => z+c) ⁻¹' e.target)
      exact hei.comp (differentiable_id.add_const c).differentiableOn (mapsTo_preimage _ _)
    have hsum : ∀ z∈closedBall (0:ℂ) (R/2), z+c∈ball (0:ℂ) R := by
      intro z hz
      rw [mem_ball_zero_iff]
      have hc' := mem_ball_zero_iff.mp hc
      have hz' := mem_closedBall_zero_iff.mp hz
      exact (norm_add_le z c).trans_lt (by linarith)
    have hTE : closedBall (0:ℂ) (R/2)⊆E.target := by
      intro z hz
      change z+c∈e.target
      exact hT (ball_subset_closedBall (hsum z hz))
    obtain ⟨a,ha,hfa⟩ := exists_boundary_limit_at_analytic_side hU hf hbij E hEi
      (half_pos hR) hTE
      (fun z hz hp => hhalf (z+c) (hsum z (ball_subset_closedBall hz)) (by simpa [hc0] using hp))
      (fun z hz hp => hline (z+c) (hsum z (ball_subset_closedBall hz)) (by simp [hc0,hp]))
    have ht : Tendsto (fun z : ℂ => z-c) (𝓝[W] c)
        (𝓝[ball (0:ℂ) (R/2)∩{z : ℂ | 0<z.re}] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have Hct : Continuous (fun z : ℂ => z-c) := continuous_id.sub continuous_const
        simpa only [sub_self] using (Hct.continuousAt (x := c)).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self (half_pos hR)))] with z hz hzc
        refine ⟨?_,?_⟩
        · simpa only [mem_ball,dist_zero_right,dist_eq_norm,sub_zero] using hzc
        · change 0<(z-c).re
          simpa only [Complex.sub_re,hc0,sub_zero] using (show 0<z.re from hz.2)
    refine ⟨a,ha,?_⟩
    have Hcomp := hfa.comp ht
    change Tendsto (fun z => f (e.symm ((z-c)+c))) (𝓝[W] c) (𝓝 a) at Hcomp
    simpa only [sub_add_cancel] using Hcomp
  have hall : ∀ c∈B, ∃ a, Tendsto H (𝓝[W] c) (𝓝 a) := by
    intro c hc
    rcases eq_or_lt_of_le (show 0≤c.re from hc.2) with hzero|hpos
    · obtain ⟨a,ha,hlimc⟩ := hlim c hc.1 hzero.symm
      exact ⟨a,hlimc⟩
    · have hcW : c∈W := ⟨ball_subset_ball (half_le_self hR.le) hc.1,hpos⟩
      exact ⟨H c,hHd.continuousOn c hcW⟩
  refine ⟨extendFrom W H,continuousOn_extendFrom hBW hall,?_,?_⟩
  · intro z hz
    exact extendFrom_extends hHd.continuousOn z ⟨ball_subset_ball (half_le_self hR.le) hz.1,hz.2⟩
  · intro z hz hz0
    obtain ⟨a,ha,hfa⟩ := hlim z hz hz0
    rwa [extendFrom_eq (hBW ⟨hz,hz0.ge⟩) hfa]

end FunctionTheory
