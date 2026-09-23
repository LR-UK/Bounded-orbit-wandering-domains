import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

open Set Metric

namespace FunctionTheory

set_option autoImplicit false

/-- The weighted maximum selection in Bloch's argument. A continuous
function on the closed unit disc has a smaller interior disc on which its
norm is at most twice its value at the centre, while radius times the
central norm retains half the initial norm. -/
theorem exists_bloch_selection {g : ℂ → ℂ}
    (hg : ContinuousOn g (closedBall (0:ℂ) 1)) (h0 : g 0≠0) :
    ∃ a : ℂ, ∃ r : ℝ,
      0<r ∧ closedBall a r ⊆ ball (0:ℂ) 1 ∧
      g a≠0 ∧ ‖g 0‖/2≤r*‖g a‖ ∧
      ∀ z∈closedBall a r, ‖g z‖≤2*‖g a‖ := by
  let w := fun z : ℂ => (1-‖z‖)*‖g z‖
  have hw : ContinuousOn w (closedBall (0:ℂ) 1) :=
    (continuousOn_const.sub continuousOn_id.norm).mul hg.norm
  obtain ⟨a,ha,hmax⟩ := (isCompact_closedBall (0:ℂ) 1).exists_isMaxOn
    ⟨0,mem_closedBall_self (by norm_num)⟩ hw
  have hga : ‖g 0‖≤(1-‖a‖)*‖g a‖ := by
    have H : (1-‖(0:ℂ)‖)*‖g 0‖≤(1-‖a‖)*‖g a‖ :=
      hmax (mem_closedBall_self (by norm_num : (0:ℝ)≤1))
    simpa only [norm_zero,sub_zero,one_mul] using H
  have h0p : 0<‖g 0‖ := norm_pos_iff.mpr h0
  have ha1 : ‖a‖<1 := by
    have hale : ‖a‖≤1 := mem_closedBall_zero_iff.mp ha
    have han : 0≤‖g a‖ := norm_nonneg _
    by_contra hn
    have heq : ‖a‖=1 := le_antisymm hale (le_of_not_gt hn)
    rw [heq,sub_self,zero_mul] at hga
    linarith
  have hga0 : g a≠0 := by
    intro heq
    rw [heq,norm_zero,mul_zero] at hga
    linarith
  let r := (1-‖a‖)/2
  have hr : 0<r := half_pos (sub_pos.mpr ha1)
  have hzbound : ∀ z∈closedBall a r, ‖z‖≤‖a‖+r := by
    intro z hz
    have H := norm_le_norm_sub_add z a
    have hd : ‖z-a‖≤r := mem_closedBall_iff_norm.mp hz
    linarith
  have hsub : closedBall a r ⊆ ball (0:ℂ) 1 := by
    intro z hz
    rw [mem_ball_zero_iff]
    have H := hzbound z hz
    dsimp only [r] at H
    linarith
  refine ⟨a,r,hr,hsub,hga0,?_,?_⟩
  · dsimp only [r]
    nlinarith
  · intro z hz
    have Hmax : (1-‖z‖)*‖g z‖≤(1-‖a‖)*‖g a‖ :=
      hmax (ball_subset_closedBall (hsub hz))
    have Hz := hzbound z hz
    have Hnorm := norm_nonneg (g z)
    have Hr : 1-‖a‖=2*r := by dsimp only [r]; ring
    have Hzr : r≤1-‖z‖ := by linarith
    have Hle : r*‖g z‖≤r*(2*‖g a‖) := by
      calc
        r*‖g z‖ ≤ (1-‖z‖)*‖g z‖ := mul_le_mul_of_nonneg_right Hzr Hnorm
        _ ≤ (1-‖a‖)*‖g a‖ := Hmax
        _ = r*(2*‖g a‖) := by rw [Hr]; ring
    exact (mul_le_mul_iff_right₀ hr).mp Hle

end FunctionTheory
