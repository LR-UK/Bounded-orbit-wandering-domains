/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.CutoffError

open Set Filter MeasureTheory InnerProductSpace Laplacian Metric
open scoped Topology ContDiff

namespace AreaDeficit

noncomputable def puncturedCutoff (P : Finset ℂ) (c : ℂ) (t : ℝ) (z : ℂ) : ℝ :=
  logCutoff c t (2*t) z - ∑ a ∈ P, logCutoff a (-2*t) (-t) z

def CutoffSeparated (P : Finset ℂ) (c : ℂ) (t : ℝ) : Prop :=
  0 < t ∧ (∀ a ∈ P, ‖a - c‖ + 2 * Real.exp (-t) < Real.exp t) ∧
    ∀ a ∈ P, ∀ b ∈ P, a ≠ b → 2 * Real.exp (-t) < ‖a - b‖

theorem eventually_cutoffSeparated (P : Finset ℂ) (c : ℂ) :
    ∀ᶠ t : ℝ in atTop, CutoffSeparated P c t := by
  have he : Tendsto (fun t : ℝ => 2 * Real.exp (-t)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul 2
  have houter : ∀ᶠ t : ℝ in atTop,
      ∀ a ∈ P, ‖a - c‖ + 2 * Real.exp (-t) < Real.exp t := by
    rw [eventually_all_finset]
    intro a _
    filter_upwards [he.eventually (eventually_lt_nhds zero_lt_one),
      Real.tendsto_exp_atTop.eventually_gt_atTop (‖a - c‖ + 1)] with t ht ht'
    linarith
  have hinner : ∀ᶠ t : ℝ in atTop,
      ∀ a ∈ P, ∀ b ∈ P, a ≠ b → 2 * Real.exp (-t) < ‖a - b‖ := by
    simp only [eventually_all_finset]
    intro a ha b hb
    by_cases hab : a = b
    · exact Eventually.of_forall (fun _ h => (h hab).elim)
    · filter_upwards [he.eventually (eventually_lt_nhds
        (norm_pos_iff.mpr (sub_ne_zero.mpr hab)))] with t ht
      exact fun _ => ht
  filter_upwards [eventually_gt_atTop (0 : ℝ), houter, hinner] with t ht ho hi
  exact ⟨ht, ho, hi⟩

theorem puncturedCutoff_contDiff (P : Finset ℂ) (c : ℂ) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ ∞ (puncturedCutoff P c t) := by
  apply (logCutoff_contDiff c (by linarith : t < 2*t)).sub
  exact ContDiff.sum (fun a _ => logCutoff_contDiff a (by linarith))

theorem puncturedCutoff_hasCompactSupport (P : Finset ℂ) (c : ℂ) {t : ℝ} (ht : 0 < t) :
    HasCompactSupport (puncturedCutoff P c t) := by
  apply (logCutoff_hasCompactSupport c (by linarith : t < 2*t)).sub
  classical
  induction P using Finset.induction_on with
  | empty => simp [HasCompactSupport]
  | @insert a P ha ih =>
    simpa only [Finset.sum_insert ha, Pi.add_def] using
      (logCutoff_hasCompactSupport a (by linarith : -2*t < -t)).add ih

theorem puncturedCutoff_bounds {P : Finset ℂ} {c z : ℂ} {t : ℝ}
    (ht : CutoffSeparated P c t) :
    0 ≤ puncturedCutoff P c t z ∧ puncturedCutoff P c t z ≤ 1 := by
  classical
  have hin : -2*t < -t := by linarith [ht.1]
  have hout : t < 2*t := by linarith [ht.1]
  by_cases hex : ∃ a ∈ P, logCutoff a (-2*t) (-t) z ≠ 0
  · obtain ⟨a, ha, haz⟩ := hex
    have hza : ‖z - a‖ < Real.exp (-t) := lt_of_not_ge
      (fun h => haz (logCutoff_eq_zero hin h))
    have hrest : ∀ b ∈ P, b ≠ a → logCutoff b (-2*t) (-t) z = 0 := by
      intro b hb hba
      apply logCutoff_eq_zero hin
      have hab := ht.2.2 a ha b hb hba.symm
      have hn : ‖a - b‖ ≤ ‖z - a‖ + ‖z - b‖ := by
        simpa only [dist_eq_norm, norm_sub_rev a z] using dist_triangle a z b
      linarith
    have hsum : (∑ b ∈ P, logCutoff b (-2*t) (-t) z) = logCutoff a (-2*t) (-t) z :=
      Finset.sum_eq_single a hrest (fun h => (h ha).elim)
    have hzc : ‖z - c‖ ≤ Real.exp t := by
      have hn : ‖z - c‖ ≤ ‖z - a‖ + ‖a - c‖ := by
        simpa only [dist_eq_norm] using dist_triangle z a c
      have he := Real.exp_pos (-t)
      have ho := ht.2.1 a ha
      linarith
    unfold puncturedCutoff
    rw [hsum, logCutoff_eq_one hout hzc]
    have hb := logCutoff_bounds a (-2*t) (-t) z
    constructor <;> linarith
  · have hs : (∑ a ∈ P, logCutoff a (-2*t) (-t) z) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      exact not_ne_iff.mp (fun h => hex ⟨a, ha, h⟩)
    simpa only [puncturedCutoff, hs, sub_zero] using logCutoff_bounds c t (2*t) z

theorem puncturedCutoff_tsupport_avoids {P : Finset ℂ} {c : ℂ} {t : ℝ}
    (ht : CutoffSeparated P c t) : tsupport (puncturedCutoff P c t) ⊆ (↑P : Set ℂ)ᶜ := by
  classical
  intro z hz
  change z ∉ P
  intro hzP
  have hzero : puncturedCutoff P c t =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [Metric.ball_mem_nhds z (Real.exp_pos (-2*t))] with w hw
    have hinner : logCutoff z (-2*t) (-t) w = 1 :=
      logCutoff_eq_one (by linarith [ht.1]) (mem_ball_iff_norm.mp hw).le
    have hsum : 1 ≤ ∑ a ∈ P, logCutoff a (-2*t) (-t) w := by
      rw [← hinner]
      exact Finset.single_le_sum (fun a _ => (logCutoff_bounds a (-2*t) (-t) w).1) hzP
    have hnonneg := (puncturedCutoff_bounds (z := w) ht).1
    have houter := (logCutoff_bounds c t (2*t) w).2
    dsimp [puncturedCutoff] at hnonneg ⊢
    linarith
  exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hz

theorem puncturedCutoff_eventually_one (P : Finset ℂ) (c : ℂ) {z : ℂ} (hz : z ∉ P) :
    ∀ᶠ t : ℝ in atTop, puncturedCutoff P c t z = 1 := by
  have he : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hinner : ∀ᶠ t : ℝ in atTop, ∀ a ∈ P, Real.exp (-t) < ‖z - a‖ := by
    rw [eventually_all_finset]
    intro a ha
    exact he.eventually (eventually_lt_nhds
      (norm_pos_iff.mpr (sub_ne_zero.mpr (ne_of_mem_of_not_mem ha hz).symm)))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hinner,
    Real.tendsto_exp_atTop.eventually_gt_atTop ‖z - c‖] with t ht hi ho
  have hs : (∑ a ∈ P, logCutoff a (-2*t) (-t) z) = 0 :=
    Finset.sum_eq_zero (fun a ha => logCutoff_eq_zero (by linarith) (hi a ha).le)
  simp only [puncturedCutoff, hs, sub_zero, logCutoff_eq_one (by linarith : t < 2*t) ho.le]

theorem laplacian_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℝ)
    (hf : ∀ a ∈ s, ContDiff ℝ 2 (f a)) (z : ℂ) :
    Δ (fun w => ∑ a ∈ s, f a w) z = ∑ a ∈ s, Δ (f a) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hs : ContDiff ℝ 2 (fun w => ∑ b ∈ s, f b w) :=
      ContDiff.sum (fun b hb => hf b (Finset.mem_insert_of_mem hb))
    have he := (hf a (Finset.mem_insert_self a s)).contDiffAt (x := z) |>.laplacian_add hs.contDiffAt
    simp only [Pi.add_def] at he
    rw [he, ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))]

theorem laplacian_puncturedCutoff (P : Finset ℂ) (c z : ℂ) {t : ℝ} (ht : 0 < t) :
    Δ (puncturedCutoff P c t) z = Δ (logCutoff c t (2*t)) z -
      ∑ a ∈ P, Δ (logCutoff a (-2*t) (-t)) z := by
  have hout : ContDiff ℝ 2 (logCutoff c t (2*t)) :=
    (logCutoff_contDiff c (by linarith)).of_le (by norm_num)
  have hin (a : ℂ) : ContDiff ℝ 2 (logCutoff a (-2*t) (-t)) :=
    (logCutoff_contDiff a (by linarith)).of_le (by norm_num)
  change Δ (fun w => logCutoff c t (2*t) w - ∑ a ∈ P, logCutoff a (-2*t) (-t) w) z = _
  have hs : ContDiff ℝ 2 (fun w => ∑ a ∈ P, logCutoff a (-2*t) (-t) w) :=
    ContDiff.sum (fun a _ => hin a)
  have he := hout.contDiffAt (x := z) |>.laplacian_sub hs.contDiffAt
  simp only [Pi.sub_def] at he
  rw [he, laplacian_finset_sum P _ (fun a _ => hin a)]

end AreaDeficit
