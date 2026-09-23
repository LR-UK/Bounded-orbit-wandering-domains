import FunctionTheory.Conformal.MonomialSymmetries
import TauCeti.Analysis.Complex.Conformal.LocalDegree
import Mathlib.Analysis.Analytic.IsolatedZeros

open Set Metric Filter Function
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- A holomorphic continuation of an injective disc map has a regular
point on every sufficiently small boundary arc, even if its derivative
vanishes at the initially chosen boundary point. -/
theorem exists_regular_circle_point_of_injOn_cap
    {f : ℂ → ℂ} {a : ℂ} (ha : ‖a‖=1) {r : ℝ} (hr : 0<r)
    (hf : AnalyticOnNhd ℂ f (ball a r))
    (hi : InjOn f (ball (0:ℂ) 1 ∩ ball a r)) :
    ∃ b : ℂ, ‖b‖=1 ∧ b∈ball a r ∧ deriv f b≠0 := by
  have hacl : a∈closure (ball (0:ℂ) 1) := by
    rw [closure_ball _ one_ne_zero]
    simpa only [mem_closedBall,dist_zero_right,ha] using (le_refl (1:ℝ))
  obtain ⟨c,hc,hca⟩ := Metric.mem_closure_iff.mp hacl r hr
  have hcb : c∈ball a r := by simpa only [mem_ball,dist_comm] using hca
  have hdc : deriv f c≠0 := TauCeti.deriv_ne_zero_of_injOn
    (hf.differentiableOn.mono inter_subset_right) (isOpen_ball.inter isOpen_ball) hi ⟨hc,hcb⟩
  have hdf : AnalyticOnNhd ℂ (deriv f) (ball a r) := hf.deriv
  have hpunct : ∀ᶠ z in 𝓝[≠] a, deriv f z≠0 := by
    rcases (hdf a (mem_ball_self hr)).eventually_eq_or_eventually_ne
      (analyticAt_const (v := (0:ℂ))) with H | H
    · exact False.elim (hdc (hdf.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
        (convex_ball a r).isPreconnected (mem_ball_self hr) H hcb))
    · exact H
  have ha0 : a≠0 := by intro H; simp [H] at ha
  let b := fun n => a*elementaryRootRotation n
  have hbt : Tendsto b atTop (𝓝 a) := by
    simpa only [b,mul_one] using
      (tendsto_const_nhds.mul elementaryRootRotation_tendsto :
        Tendsto (fun n => a*elementaryRootRotation n) atTop (𝓝 (a*1)))
  have hbne : ∀ᶠ n in atTop, b n≠a := by
    filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn H
    have he : elementaryRootRotation n=1 := mul_left_cancel₀ ha0 (by simpa only [mul_one] using H)
    exact elementaryRootRotation_ne_one (by omega) he
  have hbp : Tendsto b atTop (𝓝[≠] a) := tendsto_nhdsWithin_iff.mpr ⟨hbt,hbne⟩
  obtain ⟨n,hnb,hnd⟩ := ((hbt.eventually (ball_mem_nhds a hr)).and (hbp.eventually hpunct)).exists
  refine ⟨b n,?_,hnb,hnd⟩
  simp only [b,norm_mul,ha,elementaryRootRotation_norm,one_mul]

/-- Glue analytic functions agreeing on the overlap of two open domains.
The returned ambient representative has both prescribed restrictions. -/
theorem exists_analytic_gluing {U V : Set ℂ} {f g : ℂ → ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g V) (heq : EqOn f g (U ∩ V)) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (U ∪ V) ∧ EqOn h f U ∧ EqOn h g V := by
  classical
  let h := fun z => if z∈V then g z else f z
  have hhf : EqOn h f U := by
    intro z hz
    by_cases hzV : z∈V
    · exact (if_pos hzV).trans (heq ⟨hz,hzV⟩).symm
    · exact if_neg hzV
  have hhg : EqOn h g V := fun z hz => if_pos hz
  refine ⟨h,?_,hhf,hhg⟩
  intro z hz
  rcases hz with hz | hz
  · apply (hf z hz).congr
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (hhf hw).symm
  · apply (hg z hz).congr
    filter_upwards [hV.mem_nhds hz] with w hw
    exact (hhg hw).symm

/-- An arbitrary analytic extension of an injective closed-disc map
contains a regular boundary continuation somewhere on its boundary arc.
This removes any nonvanishing-derivative assumption at the initial point. -/
theorem exists_regular_disc_continuation_of_analytic_extension
    {f g : ℂ → ℂ} {a : ℂ} (ha : ‖a‖=1) {r : ℝ} (hr : 0<r)
    (hf : AnalyticOnNhd ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hg : AnalyticOnNhd ℂ g (ball a r))
    (hgf : EqOn g f (closedBall 0 1 ∩ ball a r)) :
    ∃ b : ℂ, ∃ ε : ℝ, ∃ e : ℂ → ℂ, ‖b‖=1 ∧ b∈ball a r ∧ 0<ε ∧
      AnalyticOnNhd ℂ e (ball 0 1 ∪ ball b ε) ∧ InjOn e (ball b ε) ∧
      EqOn e f (ball 0 1) ∧ e b=f b := by
  have hgi : InjOn g (ball (0:ℂ) 1 ∩ ball a r) := by
    intro z hz w hw H
    apply hi hz.1 hw.1
    rw [← hgf ⟨ball_subset_closedBall hz.1,hz.2⟩,
      ← hgf ⟨ball_subset_closedBall hw.1,hw.2⟩]
    exact H
  obtain ⟨b,hbn,hbr,hbd⟩ := exists_regular_circle_point_of_injOn_cap ha hr hg hgi
  obtain ⟨V,hV,hVi⟩ := (TauCeti.exists_injOn_nhds_iff_deriv_ne_zero (hg b hbr)).mpr hbd
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp (inter_mem hV (isOpen_ball.mem_nhds hbr))
  obtain ⟨e,he,hef,heg⟩ := exists_analytic_gluing isOpen_ball isOpen_ball hf hg
    (fun z hz => (hgf ⟨ball_subset_closedBall hz.1,hz.2⟩).symm)
  refine ⟨b,ε,e,hbn,hbr,hε,?_,?_,hef,?_⟩
  · exact he.mono (union_subset_union_right _ (fun z hz => (hεV hz).2))
  · intro z hz w hw H
    apply hVi (hεV hz).1 (hεV hw).1
    rw [← heg (hεV hz).2,← heg (hεV hw).2]
    exact H
  · exact (heg hbr).trans (hgf ⟨by simpa only [mem_closedBall,dist_zero_right,hbn] using (le_refl (1:ℝ)),hbr⟩)

end FunctionTheory
