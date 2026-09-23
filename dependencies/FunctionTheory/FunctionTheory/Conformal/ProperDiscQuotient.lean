import FunctionTheory.Conformal.ProperDiscBoundary
import FunctionTheory.Conformal.DiscBoundaryMaximum

open Set Metric Filter
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- A continuous function of modulus one on the circle is uniformly bounded
away from any smaller modulus in a sufficiently thin inner collar. -/
theorem exists_boundary_collar_of_continuousOn_disc
    {B : ℂ → ℂ} (hB : ContinuousOn B (closedBall (0:ℂ) 1))
    (hcircle : ∀ z : ℂ, ‖z‖=1 → ‖B z‖=1)
    {r : ℝ} (hr : r<1) :
    ∃ s : ℝ, 0<s ∧ s<1 ∧ ∀ z∈closedBall (0:ℂ) 1, s<‖z‖ → r<‖B z‖ := by
  let K : Set ℂ := {z∈closedBall (0:ℂ) 1 | ‖B z‖≤r}
  have hK : IsCompact K := (isCompact_closedBall (0:ℂ) 1).of_isClosed_subset
    (isClosed_closedBall.isClosed_le hB.norm continuousOn_const) (fun z hz => hz.1)
  have hKD : K⊆ball (0:ℂ) 1 := by
    intro z hz
    apply mem_ball_zero_iff.mpr
    have H := mem_closedBall_zero_iff.mp hz.1
    rcases H.lt_or_eq with H|H
    · exact H
    · have HB := hcircle z H
      have := hz.2
      linarith
  by_cases hne : K.Nonempty
  · obtain ⟨w,hw,hwmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
    have hwn : ‖w‖<1 := mem_ball_zero_iff.mp (hKD hw)
    refine ⟨(‖w‖+1)/2,by positivity,by linarith,?_⟩
    intro z hz hzs
    by_contra H
    have hmax : ‖z‖≤‖w‖ := hwmax ⟨hz,le_of_not_gt H⟩
    linarith
  · refine ⟨1/2,by norm_num,by norm_num,?_⟩
    intro z hz hzs
    by_contra H
    exact hne ⟨z,hz,le_of_not_gt H⟩

/-- Removing a finite inner factor with all the zeros from a proper disc map
leaves a unimodular constant. Only the residual factor is required to be
holomorphic and nonvanishing; no boundary extension of the proper map is used. -/
theorem eq_unimodular_const_of_proper_disc_factor
    {f B h : ℂ → ℂ}
    (hmap : MapsTo f (ball (0:ℂ) 1) (ball (0:ℂ) 1))
    (hproper : IsProperMap (fun z : ball (0:ℂ) 1 =>
      (⟨f z,hmap z.property⟩ : ball (0:ℂ) 1)))
    (hB : ContinuousOn B (closedBall (0:ℂ) 1))
    (hcircle : ∀ z : ℂ, ‖z‖=1 → ‖B z‖=1)
    (hsmall : ∀ z∈ball (0:ℂ) 1, ‖B z‖≤1)
    (hh : AnalyticOnNhd ℂ h (ball (0:ℂ) 1))
    (hhn : ∀ z∈ball (0:ℂ) 1, h z≠0)
    (hfactor : ∀ z∈ball (0:ℂ) 1, f z=B z*h z) :
    ∃ c : ℂ, ‖c‖=1 ∧ EqOn h (fun _ => c) (ball (0:ℂ) 1) := by
  apply eq_unimodular_const_of_disc_boundary_bounds hh hhn
  · intro ε hε
    have he : 0<1+ε := by linarith
    have ht : 1/(1+ε)<1 := (div_lt_one he).mpr (by linarith)
    obtain ⟨s,hs0,hs1,hcollar⟩ := exists_boundary_collar_of_continuousOn_disc hB hcircle ht
    refine ⟨s,hs1,?_⟩
    intro z hz hzs
    have H := hcollar z (ball_subset_closedBall hz) hzs
    have hpos : 0<‖B z‖ := (div_pos zero_lt_one he).trans H
    have Hmul : 1<‖B z‖*(1+ε) := (div_lt_iff₀ he).mp H
    have Hnorm := congrArg norm (hfactor z hz)
    rw [norm_mul] at Hnorm
    have Hf : ‖f z‖<1 := mem_ball_zero_iff.mp (hmap hz)
    exact le_of_mul_le_mul_left (Hnorm.symm.le.trans (Hf.le.trans Hmul.le)) hpos
  · intro ε hε
    have he : 0<1+ε := by linarith
    have ht : 1/(1+ε)<1 := (div_lt_one he).mpr (by linarith)
    let F : ball (0:ℂ) 1 → ball (0:ℂ) 1 := fun z => ⟨f z,hmap z.property⟩
    obtain ⟨s,hs0,hs1,hcollar⟩ := exists_boundary_collar_of_isProperMap_disc F hproper ht
    refine ⟨s,hs1,?_⟩
    intro z hz hzs
    have H : 1/(1+ε)<‖f z‖ := hcollar ⟨z,hz⟩ hzs
    have hpos : 0<‖f z‖ := (div_pos zero_lt_one he).trans H
    have Hmul : 1<‖f z‖*(1+ε) := (div_lt_iff₀ he).mp H
    have Hnorm : ‖f z‖*‖(h z)⁻¹‖=‖B z‖ := by
      rw [hfactor z hz,norm_mul,norm_inv,mul_assoc,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hhn z hz)),mul_one]
    exact le_of_mul_le_mul_left (Hnorm.le.trans ((hsmall z hz).trans Hmul.le)) hpos

end FunctionTheory
