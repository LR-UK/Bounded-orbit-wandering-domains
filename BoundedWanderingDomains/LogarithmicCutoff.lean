/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.LaplacianChain
import BoundedWanderingDomains.LogBarrier
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Constructions.HaarToSphere

open Metric Set Filter MeasureTheory InnerProductSpace Laplacian
open scoped Topology ContDiff

namespace AreaDeficit

/-- A cutoff whose transition is spread over a logarithmic annulus. -/
noncomputable def logCutoff (a : ℂ) (A B : ℝ) (z : ℂ) : ℝ :=
  if z = a then 1 else 1 - Real.smoothTransition ((Real.log ‖z - a‖ - A) / (B - A))

theorem logCutoff_bounds (a : ℂ) (A B : ℝ) (z : ℂ) :
    0 ≤ logCutoff a A B z ∧ logCutoff a A B z ≤ 1 := by
  unfold logCutoff
  split_ifs
  · constructor <;> norm_num
  · constructor <;> linarith [Real.smoothTransition.nonneg
      ((Real.log ‖z - a‖ - A) / (B - A)),
      Real.smoothTransition.le_one ((Real.log ‖z - a‖ - A) / (B - A))]

theorem logCutoff_eq_one {a z : ℂ} {A B : ℝ} (hAB : A < B)
    (hz : ‖z - a‖ ≤ Real.exp A) : logCutoff a A B z = 1 := by
  by_cases hza : z = a
  · simp [logCutoff, hza]
  have hp : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hza)
  have hl : Real.log ‖z - a‖ ≤ A := by
    simpa using Real.log_le_log hp hz
  simp only [logCutoff, ite_eq_right hza]
  rw [Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hl) (sub_pos.mpr hAB).le)]
  ring

theorem logCutoff_eq_zero {a z : ℂ} {A B : ℝ} (hAB : A < B)
    (hz : Real.exp B ≤ ‖z - a‖) : logCutoff a A B z = 0 := by
  have hp : 0 < ‖z - a‖ := (Real.exp_pos B).trans_le hz
  have hza : z ≠ a := sub_ne_zero.mp (norm_pos_iff.mp hp)
  have hl : B ≤ Real.log ‖z - a‖ := by
    simpa using Real.log_le_log (Real.exp_pos B) hz
  simp only [logCutoff, ite_eq_right hza]
  rw [Real.smoothTransition.one_of_one_le
    ((le_div_iff₀ (sub_pos.mpr hAB)).mpr (by linarith))]
  ring

theorem logCutoff_contDiff (a : ℂ) {A B : ℝ} (hAB : A < B) :
    ContDiff ℝ ∞ (logCutoff a A B) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hza : z = a
  · subst z
    have he : logCutoff a A B =ᶠ[𝓝 a] (fun _ => 1) := by
      filter_upwards [Metric.ball_mem_nhds a (Real.exp_pos A)] with w hw
      exact logCutoff_eq_one hAB (by simpa [dist_eq_norm] using (mem_ball.mp hw).le)
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hu : ContDiffAt ℝ ∞ (fun w : ℂ => Real.log ‖w - a‖) z :=
      ((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr hza)).log
        (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hza))
    have hd : ContDiffAt ℝ ∞
        (fun w : ℂ => 1 - Real.smoothTransition ((Real.log ‖w - a‖ - A) / (B - A))) z :=
      contDiffAt_const.sub (Real.smoothTransition.contDiff.contDiffAt.comp z
        ((hu.sub contDiffAt_const).div_const _))
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hza] with w hw
    simp [logCutoff, hw]

theorem logCutoff_tsupport {a : ℂ} {A B : ℝ} (hAB : A < B) :
    tsupport (logCutoff a A B) ⊆ closedBall a (Real.exp B) := by
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  by_contra hn
  have hle : Real.exp B ≤ ‖z - a‖ := by
    have hn' : ¬ ‖z - a‖ ≤ Real.exp B := by
      simpa [mem_closedBall, dist_eq_norm] using hn
    exact le_of_not_ge hn'
  exact hz (logCutoff_eq_zero hAB hle)

theorem logCutoff_hasCompactSupport (a : ℂ) {A B : ℝ} (hAB : A < B) :
    HasCompactSupport (logCutoff a A B) :=
  (isCompact_closedBall a (Real.exp B)).of_isClosed_subset
    (isClosed_tsupport _) (logCutoff_tsupport hAB)

theorem pd_log_norm {z : ℂ} (hz : z ≠ 0) (v : ℂ) :
    pd (fun w : ℂ => Real.log ‖w‖) v z = inner ℝ z v / ‖z‖ ^ 2 := by
  have hsq : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have h := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.log hsq).const_mul (1 / 2)
  have he : (fun w : ℂ => (1 / 2 : ℝ) * Real.log (‖w‖ ^ 2)) = (fun w : ℂ => Real.log ‖w‖) := by
    funext w
    rw [Real.log_pow]
    ring
  rw [he] at h
  unfold pd
  rw [h.fderiv]
  simp only [smul_apply, smul_eq_mul, two_smul, add_apply]
  change (1 / 2 : ℝ) * ((‖z‖ ^ 2)⁻¹ * (inner ℝ z v + inner ℝ z v)) = _
  ring

end AreaDeficit
