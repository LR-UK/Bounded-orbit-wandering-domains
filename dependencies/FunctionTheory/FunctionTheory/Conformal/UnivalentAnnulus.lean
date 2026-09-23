import TauCeti.Analysis.Complex.Conformal.Rouche
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # Image disks and uniform nonvanishing on an outer annulus

Rouché's theorem puts a smaller disk inside the image of a map close to the
identity on a circle. Injectivity then excludes small values outside that
circle. Local uniform convergence to the identity makes this estimate uniform
along a tail of a sequence, as needed before reflecting conformal maps.
-/

open Set Metric Filter Complex
open scoped Topology

namespace FunctionTheory

theorem ball_subset_image_of_close_to_identity_on_sphere
    {f : ℂ → ℂ} {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (hclose : ∀ z ∈ sphere (0 : ℂ) r, ‖f z - z‖ < ε) :
    ball (0 : ℂ) (r - ε) ⊆ f '' ball 0 r := by
  intro w hw
  have hwn : ‖w‖ < r - ε := by simpa only [mem_ball, dist_zero_right] using hw
  have hwr : w ∈ ball (0 : ℂ) r := by
    rw [mem_ball, dist_zero_right]
    linarith
  have hequiv := TauCeti.rouche_exists_eq_zero_iff (c := (0 : ℂ))
    (f := fun z => z - w) (g := fun z => f z - w) hr
    ((analyticOnNhd_id).sub analyticOnNhd_const :
      AnalyticOnNhd ℂ (fun z => z - w) (closedBall 0 r))
    (hf.sub analyticOnNhd_const) (by
      intro z hz
      have hzn : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
      have hzw : ε < ‖z - w‖ := by
        have ht := norm_sub_norm_le z w
        rw [hzn] at ht
        linarith
      have heq : (z - w) - (f z - w) = -(f z - z) := by ring
      change ‖(z - w) - (f z - w)‖ < ‖z - w‖
      rw [heq, norm_neg]
      exact (hclose z hz).trans hzw)
  obtain ⟨z, hz, hzero⟩ := hequiv.mp ⟨w, hwr, sub_self w⟩
  exact ⟨z, hz, sub_eq_zero.mp hzero⟩

theorem norm_ge_on_outer_annulus_of_close_to_identity
    {f : ℂ → ℂ} {r ε : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hclose : ∀ z ∈ sphere (0 : ℂ) r, ‖f z - z‖ < ε) :
    ∀ z ∈ ball (0 : ℂ) 1, r ≤ ‖z‖ → r - ε ≤ ‖f z‖ := by
  have hrsub : closedBall (0 : ℂ) r ⊆ ball 0 1 := closedBall_subset_ball hr1
  have hcover := ball_subset_image_of_close_to_identity_on_sphere hr hε
    ((hf.analyticOnNhd isOpen_ball).mono hrsub) hclose
  intro z hz hzr
  by_contra hn
  have hsmall : f z ∈ ball (0 : ℂ) (r - ε) := by
    simpa only [mem_ball, dist_zero_right] using lt_of_not_ge hn
  obtain ⟨w, hw, hwf⟩ := hcover hsmall
  have hw1 : w ∈ ball (0 : ℂ) 1 := hrsub (ball_subset_closedBall hw)
  have hwz : w = z := hi hw1 hz hwf
  subst w
  exact (show ‖z‖ < r by simpa only [mem_ball, dist_zero_right] using hw).not_ge hzr

theorem eventually_norm_ge_on_outer_annulus
    {F : ℕ → ℂ → ℂ} {r ε : ℝ} (hr : 0 < r) (hr1 : r < 1) (hε : 0 < ε)
    (hF : ∀ n, DifferentiableOn ℂ (F n) (ball 0 1))
    (hi : ∀ n, InjOn (F n) (ball 0 1))
    (hconv : TendstoLocallyUniformlyOn F (fun z => z) atTop (ball 0 1)) :
    ∀ᶠ n in atTop, ∀ z ∈ ball (0 : ℂ) 1, r ≤ ‖z‖ → r - ε ≤ ‖F n z‖ := by
  have hsub : sphere (0 : ℂ) r ⊆ ball 0 1 :=
    sphere_subset_closedBall.trans (closedBall_subset_ball hr1)
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (isCompact_sphere (0 : ℂ) r)).mp (hconv.mono hsub)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) ε hε] with n hn
  apply norm_ge_on_outer_annulus_of_close_to_identity hr hr1 hε (hF n) (hi n)
  intro z hz
  rw [norm_sub_rev]
  simpa only [dist_eq_norm] using hn z hz

end FunctionTheory
