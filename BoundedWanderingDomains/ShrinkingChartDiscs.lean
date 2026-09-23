/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.ShrinkingImages
import BoundedWanderingDomains.ChartDiscs

open Set Metric Function Filter
open scoped Topology

namespace AreaDeficit

/-- Fixed intrinsic discs in disjoint uniformly bounded simply connected
chart domains shrink about their marked points. The domains themselves
need not be relatively compact in a smaller ambient set. -/
theorem disjoint_bounded_chart_discs_shrink
    {U : ℕ → Set ℂ} {u : ℕ → ℂ → ℂ} {z : ℕ → ℂ} {M : ℝ}
    (hU : ∀ n, IsOpen (U n))
    (hu : ∀ n, DifferentiableOn ℂ (u n) (U n))
    (hub : ∀ n, BijOn (u n) (U n) (ball 0 1))
    (hz : ∀ n, z n ∈ U n) (hu0 : ∀ n, u n (z n) = 0)
    (hb : ∀ n x, x ∈ U n → ‖x‖ ≤ M)
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m)))
    {r : ℝ} (_hr : 0 ≤ r) (hr1 : r < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ chartDisc (u n) (U n) r, dist x (z n) < ε := by
  let p : ℕ → ℂ → ℂ := fun n => invFunOn (u n) (U n)
  have hpm : ∀ n, MapsTo (p n) (ball 0 1) (U n) := by
    intro n w hw
    exact invFunOn_mem ((hub n).surjOn hw)
  have hpd : ∀ n, DifferentiableOn ℂ (p n) (ball 0 1) := by
    intro n
    simpa only [(hub n).image_eq] using (hu n).invFunOn (hU n) (hub n).injOn
  have hp0 : ∀ n, p n 0 = z n := by
    intro n
    rw [← hu0 n]
    exact (hub n).injOn.leftInvOn_invFunOn (hz n)
  have hdis' : Pairwise (fun n m => Disjoint (p n '' ball 0 1) (p m '' ball 0 1)) := by
    intro n m hne
    exact (hdis hne).mono (hpm n).image_subset (hpm m).image_subset
  have hshrink := disjoint_bounded_images_shrink isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected
    (mem_ball_self zero_lt_one) (isCompact_closedBall (0 : ℂ) r)
    (closedBall_subset_ball hr1) hpd (fun n w hw => hb n _ (hpm n hw)) hdis'
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hshrink ε hε] with n hn x hx
  have hw : u n x ∈ closedBall (0 : ℂ) r := ball_subset_closedBall hx.2
  have hi : p n (u n x) = x := (hub n).injOn.leftInvOn_invFunOn hx.1
  simpa only [hi, hp0, dist_zero_right, dist_eq_norm, zero_sub, norm_neg] using hn (u n x) hw

/-- If the marked points stay in a smaller closed disc, every fixed
intrinsic disc is eventually contained in a single intermediate compact disc. -/
theorem chart_discs_eventually_in_fixed_closedBall
    {U : ℕ → Set ℂ} {u : ℕ → ℂ → ℂ} {z : ℕ → ℂ} {M R S : ℝ}
    (hU : ∀ n, IsOpen (U n))
    (hu : ∀ n, DifferentiableOn ℂ (u n) (U n))
    (hub : ∀ n, BijOn (u n) (U n) (ball 0 1))
    (hz : ∀ n, z n ∈ U n) (hu0 : ∀ n, u n (z n) = 0)
    (hb : ∀ n x, x ∈ U n → ‖x‖ ≤ M)
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m)))
    (hzn : ∀ n, ‖z n‖ ≤ R) (hRS : R < S)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ∀ᶠ n in atTop, chartDisc (u n) (U n) r ⊆ closedBall 0 S := by
  filter_upwards [disjoint_bounded_chart_discs_shrink hU hu hub hz hu0 hb hdis hr hr1
    (sub_pos.mpr hRS)] with n hn x hx
  apply mem_closedBall_zero_iff.mpr
  have hdist := hn x hx
  have hnorm : ‖x‖ ≤ dist x (z n) + ‖z n‖ := by
    simpa only [dist_eq_norm, add_comm] using norm_le_insert' x (z n)
  linarith [hzn n]

end AreaDeficit
