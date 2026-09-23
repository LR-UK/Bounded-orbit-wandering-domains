import GreenIdentity
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Normed.Group.Bounded

open MeasureTheory Filter Set InnerProductSpace Laplacian
open scoped Topology ContDiff

namespace AreaDeficit

noncomputable def logBarrier (F : Finset ℂ) (C : ℝ) (z : ℂ) : ℝ :=
  (∑ a ∈ F, Real.log ‖z - a‖) - C

theorem log_norm_harmonic {a z : ℂ} (hz : z ≠ a) :
    HarmonicAt (fun x : ℂ => Real.log ‖x - a‖) z :=
  (analyticAt_id.sub analyticAt_const).harmonicAt_log_norm (sub_ne_zero.mpr hz)

theorem sum_log_harmonic (F : Finset ℂ) {z : ℂ} (hz : z ∉ F) :
    HarmonicAt (fun x : ℂ => ∑ a ∈ F, Real.log ‖x - a‖) z := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
    simp only [Finset.mem_insert, not_or] at hz
    simpa only [Finset.sum_insert ha, Pi.add_def] using
      (log_norm_harmonic hz.1).add (ih hz.2)

theorem logBarrier_harmonic (F : Finset ℂ) (C : ℝ) {z : ℂ} (hz : z ∉ F) :
    HarmonicAt (logBarrier F C) z :=
  (sum_log_harmonic F hz).sub (harmonicAt_const C)

theorem logBarrier_nonpos (F : Finset ℂ) {R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R) :
    logBarrier F (∑ a ∈ F, (R + ‖a‖)) z ≤ 0 := by
  apply sub_nonpos.mpr
  apply Finset.sum_le_sum
  intro a _
  exact (Real.log_le_self (norm_nonneg _)).trans
    ((norm_sub_le z a).trans (by linarith))

theorem log_norm_tendsto_atBot (a : ℂ) :
    Tendsto (fun z : ℂ => Real.log ‖z - a‖) (𝓝[≠] a) atBot := by
  apply Real.tendsto_log_nhdsGT_zero.comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Tendsto (fun z : ℂ => ‖z - a‖) (𝓝 a) (𝓝 0) := by
      simpa using (continuousAt_id.sub
        (show ContinuousAt (fun _ : ℂ => a) a from continuousAt_const)).norm.tendsto
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hz)

/-- The logarithmic barrier becomes arbitrarily negative near each puncture. -/
theorem logBarrier_eventually_le (F : Finset ℂ) (C : ℝ) {a : ℂ} (ha : a ∈ F)
    (B : ℝ) : ∀ᶠ z in 𝓝[≠] a, logBarrier F C z ≤ B := by
  have hrest : ContinuousAt (fun z : ℂ => ∑ p ∈ F.erase a, Real.log ‖z - p‖) a :=
    (sum_log_harmonic (F.erase a) (by simp)).1.continuousAt
  let D : ℝ := (∑ p ∈ F.erase a, Real.log ‖a - p‖) + 1
  have hr : ∀ᶠ z in 𝓝 a, (∑ p ∈ F.erase a, Real.log ‖z - p‖) < D :=
    hrest.tendsto.eventually (eventually_lt_nhds (by dsimp [D]; linarith))
  have hl : ∀ᶠ z in 𝓝[≠] a, Real.log ‖z - a‖ ≤ B + C - D :=
    (log_norm_tendsto_atBot a).eventually (eventually_le_atBot _)
  filter_upwards [hl, hr.filter_mono nhdsWithin_le_nhds] with z hz hzr
  unfold logBarrier
  rw [← Finset.sum_erase_add _ _ ha]
  linarith

end AreaDeficit
