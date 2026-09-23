/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Potential.PoissonDirichlet
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Continuous subharmonic functions and Perron's modification

A continuous function `f` on an open set `U ⊆ ℂ` is **subharmonic** when it satisfies the
sub-mean-value inequality: `f c ≤ ⨍_{|z-c|=r} f` for every circle bounding a closed disk in `U`.
Restricting to *continuous* subharmonic functions (rather than the general upper-semicontinuous,
possibly `-∞` class) is sufficient for constructing the bounded harmonic potential of a ring domain
by Perron's method, and avoids the integrability technicalities of the general theory.

This file provides the four ingredients Perron's method needs:

* harmonic functions are subharmonic (the mean-value equality);
* the pointwise maximum of two subharmonic functions is subharmonic;
* the **maximum principle**: a continuous subharmonic function on a bounded open set is bounded by
  any boundary bound;
* **Poisson modification**: lifting a subharmonic function to its Poisson integral on an open disk
  keeps it subharmonic, does not decrease it, and makes it harmonic on that disk.

## Main definitions

* `SubharmonicOn f U` — `f` is continuous on `U` and satisfies the sub-mean-value inequality;
* `poissonModify f c R` — `f` replaced by its Poisson integral on the open disk `ball c R`.

## Main statements

* `HarmonicOnNhd.subharmonicOn` — harmonic ⟹ subharmonic;
* `subharmonicOn_max` — `max f g` is subharmonic when `f`, `g` are;
* `SubharmonicOn.le_of_frontier_le` — the maximum principle (boundary bound propagates inward);
* `poissonModify_ge`, `poissonModify_harmonicOn`, `SubharmonicOn.poissonModify` — Poisson
  modification.
-/

open MeasureTheory Filter Metric Topology
open scoped Real Topology

namespace RiemannDynamics

/-- A continuous function `f : ℂ → ℝ` is **subharmonic** on an open set `U` when it satisfies the
sub-mean-value inequality `f c ≤ Real.circleAverage f c r` for every centre `c ∈ U` and radius
`r > 0` whose closed disk lies in `U`. (Continuity is imposed as part of the definition; the general
upper-semicontinuous theory is not needed for the bounded potentials built here.) -/
def SubharmonicOn (f : ℂ → ℝ) (U : Set ℂ) : Prop :=
  ContinuousOn f U ∧ ∀ c ∈ U, ∀ r : ℝ, 0 < r → Metric.closedBall c r ⊆ U →
    f c ≤ Real.circleAverage f c r

/-- **Harmonic functions are subharmonic.** A function harmonic on an open neighbourhood of `U`
satisfies the mean-value *equality*, hence the sub-mean-value inequality. -/
theorem HarmonicOnNhd.subharmonicOn {f : ℂ → ℝ} {U : Set ℂ}
    (hf : InnerProductSpace.HarmonicOnNhd f U) : SubharmonicOn f U := by
  refine ⟨hf.continuousOn, ?_⟩
  intro c _ r hr hsub
  have habs : |r| = r := abs_of_pos hr
  have hmono : InnerProductSpace.HarmonicOnNhd f (Metric.closedBall c |r|) := by
    rw [habs]; exact hf.mono hsub
  rw [InnerProductSpace.HarmonicOnNhd.circleAverage_eq hmono]

/-- **The pointwise maximum of two subharmonic functions is subharmonic.** The max of two continuous
functions is continuous, and `max f g c ≤ max (⨍ f) (⨍ g) ≤ ⨍ (max f g)` by monotonicity of the
circle average. -/
theorem subharmonicOn_max {f g : ℂ → ℝ} {U : Set ℂ}
    (hf : SubharmonicOn f U) (hg : SubharmonicOn g U) :
    SubharmonicOn (fun z => max (f z) (g z)) U := by
  obtain ⟨hfc, hfmv⟩ := hf
  obtain ⟨hgc, hgmv⟩ := hg
  refine ⟨fun x hx => (hfc x hx).max (hgc x hx), ?_⟩
  intro c hc r hr hsub
  -- The sphere lies inside `U`, so `f`, `g`, and `max f g` are circle-integrable.
  have hsphere : Metric.sphere c r ⊆ U :=
    (Metric.sphere_subset_closedBall).trans hsub
  have hfci : CircleIntegrable f c r :=
    (hfc.mono hsphere).circleIntegrable hr.le
  have hgci : CircleIntegrable g c r :=
    (hgc.mono hsphere).circleIntegrable hr.le
  have hmaxcont : ContinuousOn (fun z => max (f z) (g z)) (Metric.sphere c r) :=
    fun x hx => ((hfc.mono hsphere) x hx).max ((hgc.mono hsphere) x hx)
  have hmci : CircleIntegrable (fun z => max (f z) (g z)) c r :=
    hmaxcont.circleIntegrable hr.le
  have habs : |r| = r := abs_of_pos hr
  -- `⨍ f ≤ ⨍ (max f g)` and `⨍ g ≤ ⨍ (max f g)`.
  have hfle : Real.circleAverage f c r ≤ Real.circleAverage (fun z => max (f z) (g z)) c r := by
    apply Real.circleAverage_mono hfci hmci
    intro x _; exact le_max_left _ _
  have hgle : Real.circleAverage g c r ≤ Real.circleAverage (fun z => max (f z) (g z)) c r := by
    apply Real.circleAverage_mono hgci hmci
    intro x _; exact le_max_right _ _
  -- Combine with the sub-mean-value inequalities for `f` and `g`.
  have hf' : f c ≤ Real.circleAverage (fun z => max (f z) (g z)) c r :=
    le_trans (hfmv c hc r hr hsub) hfle
  have hg' : g c ≤ Real.circleAverage (fun z => max (f z) (g z)) c r :=
    le_trans (hgmv c hc r hr hsub) hgle
  exact max_le hf' hg'

/-- **The maximum principle for continuous subharmonic functions.** A continuous subharmonic
function on a nonempty bounded open set `U`, continuous up to the closure, is bounded throughout `U`
by any bound it satisfies on the frontier. (If `f ≤ M` on `∂U` then `f ≤ M` on `U`: an interior
point where `f` exceeds its frontier supremum would be a strict interior maximum, contradicting the
sub-mean-value inequality on a small circle.) -/
theorem SubharmonicOn.le_of_frontier_le {f : ℂ → ℝ} {U : Set ℂ} (hUopen : IsOpen U)
    (hUbdd : Bornology.IsBounded U) (hf : SubharmonicOn f U)
    (hfc : ContinuousOn f (closure U)) {M : ℝ} (hle : ∀ z ∈ frontier U, f z ≤ M) :
    ∀ z ∈ U, f z ≤ M := by
  obtain ⟨hfcU, hfmv⟩ := hf
  -- `K = closure U` is compact (`U` bounded), and `frontier U = K \ U`.
  have hKcl : IsClosed (closure U) := isClosed_closure
  have hKcompact : IsCompact (closure U) :=
    isCompact_of_isClosed_isBounded hKcl hUbdd.closure
  have hfront : frontier U = closure U \ U := hUopen.frontier_eq
  intro c₀ hc₀
  by_contra hcon
  rw [not_le] at hcon
  -- The strictly subharmonic perturbation `q z = ‖z - c₀‖²` (with `q c₀ = 0`).
  set q : ℂ → ℝ := fun z => ‖z - c₀‖ ^ 2 with hq
  -- Exact circle average of `q`: `⨍_{sphere a ρ} q = ‖a - c₀‖² + ρ²`.
  have hqavg : ∀ (a : ℂ) (ρ : ℝ),
      Real.circleAverage q a ρ = ‖a - c₀‖ ^ 2 + ρ ^ 2 := by
    intro a ρ
    have hcm : ∀ θ : ℝ, ‖circleMap a ρ θ - c₀‖ ^ 2
        = (‖a - c₀‖ ^ 2 + ρ ^ 2) + 2 * ρ * (a - c₀).re * Real.cos θ
          + 2 * ρ * (a - c₀).im * Real.sin θ := by
      intro θ
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [circleMap, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
      nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [Real.circleAverage_def]
    have hinteq : (∫ θ in (0 : ℝ)..(2 * π), q (circleMap a ρ θ))
        = ∫ θ in (0 : ℝ)..(2 * π), ((‖a - c₀‖ ^ 2 + ρ ^ 2)
            + 2 * ρ * (a - c₀).re * Real.cos θ + 2 * ρ * (a - c₀).im * Real.sin θ) :=
      intervalIntegral.integral_congr (fun θ _ => hcm θ)
    rw [hinteq]
    have hc1 : IntervalIntegrable (fun _ : ℝ => ‖a - c₀‖ ^ 2 + ρ ^ 2) volume 0 (2 * π) :=
      continuous_const.intervalIntegrable _ _
    have hc2 : IntervalIntegrable (fun θ : ℝ => 2 * ρ * (a - c₀).re * Real.cos θ)
        volume 0 (2 * π) := by
      have : Continuous fun θ : ℝ => 2 * ρ * (a - c₀).re * Real.cos θ := by fun_prop
      exact this.intervalIntegrable _ _
    have hc3 : IntervalIntegrable (fun θ : ℝ => 2 * ρ * (a - c₀).im * Real.sin θ)
        volume 0 (2 * π) := by
      have : Continuous fun θ : ℝ => 2 * ρ * (a - c₀).im * Real.sin θ := by fun_prop
      exact this.intervalIntegrable _ _
    rw [intervalIntegral.integral_add (hc1.add hc2) hc3, intervalIntegral.integral_add hc1 hc2,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_cos, integral_sin]
    simp only [Real.sin_zero, Real.sin_two_pi, Real.cos_zero, Real.cos_two_pi, smul_eq_mul]
    have hpi : (2 * π) ≠ 0 := by positivity
    field_simp
    ring
  -- `q` is continuous everywhere.
  have hqcont : Continuous q := by rw [hq]; fun_prop
  -- A uniform bound `0 ≤ ‖q z‖ ≤ C` on `closure U`.
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn (f := q) hqcont.continuousOn
  have hC0 : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC c₀ (subset_closure hc₀))
  have hqle : ∀ z ∈ closure U, q z ≤ C := fun z hz => le_trans (le_abs_self _)
    (by simpa [Real.norm_eq_abs] using hC z hz)
  -- Choose `ε > 0` so small that `f c₀ > M + ε C`.
  set ε : ℝ := (f c₀ - M) / (C + 1) with hε
  have hεpos : 0 < ε := by
    rw [hε]; apply div_pos (by linarith [hcon]) (by positivity)
  have hperturb : M + ε * C < f c₀ := by
    rw [hε]
    have hCC : C / (C + 1) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    have : (f c₀ - M) / (C + 1) * C = (f c₀ - M) * (C / (C + 1)) := by ring
    rw [this]
    nlinarith [hcon, hCC]
  -- The perturbed function `g = f + ε q` is continuous on the compact `closure U`.
  set g : ℂ → ℝ := fun z => f z + ε * q z with hg
  have hgcont : ContinuousOn g (closure U) := by
    apply ContinuousOn.add hfc
    exact continuousOn_const.mul hqcont.continuousOn
  -- `g` attains its maximum on `closure U` at some `p`.
  obtain ⟨p, hpK, hpmax⟩ := hKcompact.exists_isMaxOn
    ⟨c₀, subset_closure hc₀⟩ hgcont
  -- The maximum point `p` cannot lie in the open set `U`.
  have hpU : p ∉ U := by
    intro hpUmem
    -- A small circle `closedBall p ρ ⊆ U`.
    obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.1 hUopen p hpUmem
    set r := ρ / 2 with hr
    have hrpos : 0 < r := by rw [hr]; linarith
    have hballsub : Metric.closedBall p r ⊆ U := by
      intro z hz
      apply hρsub
      rw [Metric.mem_ball]
      rw [Metric.mem_closedBall] at hz
      have : r < ρ := by rw [hr]; linarith
      linarith
    have hspheresub : Metric.sphere p r ⊆ U :=
      (Metric.sphere_subset_closedBall).trans hballsub
    -- `f` and `q` are circle-integrable on this circle.
    have hfci : CircleIntegrable f p r := (hfcU.mono hspheresub).circleIntegrable hrpos.le
    have hgci : CircleIntegrable g p r := by
      apply ((hfcU.mono hspheresub).add (continuousOn_const.mul
        hqcont.continuousOn)).circleIntegrable hrpos.le
    -- Strict sub-mean-value inequality for `g`: `g p < ⨍ g`.
    have hfmean : f p ≤ Real.circleAverage f p r := hfmv p hpUmem r hrpos hballsub
    have hqmean : Real.circleAverage q p r = q p + r ^ 2 := by
      rw [hqavg p r, hq]
    have hgavg : Real.circleAverage g p r
        = Real.circleAverage f p r + ε * (q p + r ^ 2) := by
      rw [hg]
      rw [show (fun z => f z + ε * q z) = f + (fun z => ε * q z) from rfl]
      rw [Real.circleAverage_add hfci (by
        apply (((continuousOn_const).mul hqcont.continuousOn).circleIntegrable hrpos.le))]
      rw [show (fun z => ε * q z) = (fun z => ε • q z) from funext fun z => by simp [smul_eq_mul]]
      rw [Real.circleAverage_fun_smul, hqmean, smul_eq_mul]
    have hgstrict : g p < Real.circleAverage g p r := by
      rw [hgavg, hg]
      have : ε * q p < ε * (q p + r ^ 2) := by
        apply mul_lt_mul_of_pos_left _ hεpos
        nlinarith [hrpos]
      simp only
      linarith [hfmean]
    -- But `p` is a maximum, so `⨍ g ≤ g p`.
    have hgmax_avg : Real.circleAverage g p r ≤ g p := by
      apply Real.circleAverage_mono_on_of_le_circle hgci
      intro x hx
      have hxU : x ∈ closure U := subset_closure (hspheresub (by
        rwa [abs_of_pos hrpos] at hx))
      exact hpmax hxU
    linarith [hgstrict, hgmax_avg]
  -- Hence `p ∈ frontier U`, so `f p ≤ M`.
  have hpfront : p ∈ frontier U := by rw [hfront]; exact ⟨hpK, hpU⟩
  have hfpM : f p ≤ M := hle p hpfront
  -- `g c₀ ≤ g p` gives `f c₀ ≤ M + ε C`, contradicting the choice of `ε`.
  have hmaxc₀ : g c₀ ≤ g p := hpmax (subset_closure hc₀)
  have hgc₀ : g c₀ = f c₀ := by
    rw [hg]; simp only [hq, sub_self, norm_zero]; ring
  have hgp : g p ≤ M + ε * C := by
    rw [hg]; simp only
    have hqpC : q p ≤ C := hqle p hpK
    nlinarith [hfpM, mul_le_mul_of_nonneg_left hqpC hεpos.le, hεpos]
  rw [hgc₀] at hmaxc₀
  linarith [hmaxc₀, hgp, hperturb]

open Classical in
/-- **Poisson modification.** Replace `f` by its Poisson integral on the open disk `ball c R`
(leaving it unchanged on the boundary circle and outside): `poissonModify f c R z =
poissonIntegral f c R z` for `z` in the open disk and `f z` otherwise. Using the *open* disk keeps
the modification continuous across the boundary circle (the Poisson integral tends to `f` there),
so `f - poissonModify` is continuous on the closed disk and vanishes on the circle. The local
harmonic-replacement operator of Perron's method. -/
noncomputable def poissonModify (f : ℂ → ℝ) (c : ℂ) (R : ℝ) : ℂ → ℝ :=
  fun z => if z ∈ Metric.ball c R then poissonIntegral f c R z else f z

/-- **Poisson modification does not decrease a subharmonic function.** On the disk where it acts,
the Poisson integral of the boundary values of a subharmonic `f` dominates `f` (the maximum
principle applied to `f` minus the Poisson solution, which agree on the boundary circle). Off the
disk it equals `f`. -/
theorem poissonModify_ge {f : ℂ → ℝ} {U : Set ℂ} (hf : SubharmonicOn f U)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hball : Metric.closedBall c R ⊆ U) :
    ∀ z ∈ U, f z ≤ poissonModify f c R z := by
  classical
  obtain ⟨hfcU, hfmv⟩ := hf
  have hRne : R ≠ 0 := ne_of_gt hR
  have hsphere : Metric.sphere c R ⊆ U := (Metric.sphere_subset_closedBall).trans hball
  have hfsphere : ContinuousOn f (Metric.sphere c R) := hfcU.mono hsphere
  -- `poissonModify` is harmonic on the open ball.
  have hpmharm : InnerProductSpace.HarmonicOnNhd (poissonModify f c R) (Metric.ball c R) := by
    have hharm : InnerProductSpace.HarmonicOnNhd (poissonIntegral f c R) (Metric.ball c R) :=
      poissonIntegral_harmonicOn f c hR hfsphere
    intro w hw
    have heqw : poissonModify f c R =ᶠ[𝓝 w] poissonIntegral f c R := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hw] with z hz
      simp only [poissonModify, ite_eq_left hz]
    rw [InnerProductSpace.harmonicAt_congr_nhds heqw]
    exact hharm w hw
  -- `poissonModify` is continuous on the closed ball.
  have hpmcont : ContinuousOn (poissonModify f c R) (Metric.closedBall c R) := by
    have hPcont : ContinuousOn (poissonIntegral f c R) (Metric.ball c R) :=
      (poissonIntegral_harmonicOn f c hR hfsphere).continuousOn
    have hsplit : Metric.closedBall c R = Metric.ball c R ∪ Metric.sphere c R :=
      Metric.ball_union_sphere.symm
    intro ζ hζ
    rw [Metric.mem_closedBall] at hζ
    rcases lt_or_eq_of_le hζ with hlt | heq
    · have hζball : ζ ∈ Metric.ball c R := Metric.mem_ball.2 hlt
      have heqf : poissonModify f c R =ᶠ[𝓝 ζ] poissonIntegral f c R := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hζball] with z hz
        simp only [poissonModify, ite_eq_left hz]
      have hca : ContinuousAt (poissonIntegral f c R) ζ :=
        (hPcont ζ hζball).continuousAt (Metric.isOpen_ball.mem_nhds hζball)
      exact (hca.congr heqf.symm).continuousWithinAt
    · have hζsphere : ζ ∈ Metric.sphere c R := Metric.mem_sphere.2 heq
      have hnotball : ζ ∉ Metric.ball c R := by rw [Metric.mem_ball, heq]; exact lt_irrefl _
      have hpmζ : poissonModify f c R ζ = f ζ := by simp only [poissonModify, ite_eq_right hnotball]
      rw [hsplit]
      apply ContinuousWithinAt.union
      · have htend : Tendsto (poissonIntegral f c R) (𝓝[Metric.ball c R] ζ) (𝓝 (f ζ)) :=
          poissonIntegral_tendsto_boundary f c hR hfsphere hζsphere
        have heqball :
            poissonModify f c R =ᶠ[𝓝[Metric.ball c R] ζ] poissonIntegral f c R := by
          filter_upwards [self_mem_nhdsWithin] with z hz
          simp only [poissonModify, ite_eq_left hz]
        rw [ContinuousWithinAt, hpmζ]
        exact htend.congr' heqball.symm
      · have hcwf : ContinuousWithinAt f (Metric.sphere c R) ζ := hfsphere ζ hζsphere
        apply hcwf.congr (fun z hz => ?_) hpmζ
        have : z ∉ Metric.ball c R := by
          rw [Metric.mem_ball, Metric.mem_sphere.1 hz]; exact lt_irrefl _
        simp only [poissonModify, ite_eq_right this]
  -- The difference `g = f - poissonModify` is subharmonic on the ball.
  set g : ℂ → ℝ := fun w => f w - poissonModify f c R w with hg
  have hgsub : SubharmonicOn g (Metric.ball c R) := by
    refine ⟨?_, ?_⟩
    · apply ContinuousOn.sub (hfcU.mono (Metric.ball_subset_closedBall.trans hball))
      exact hpmcont.mono Metric.ball_subset_closedBall
    · intro c₁ hc₁ ρ hρ hballρ
      -- `f` sub-mean-value and `poissonModify` mean-value equality on `sphere c₁ ρ`.
      have hballρU : Metric.closedBall c₁ ρ ⊆ U :=
        hballρ.trans (Metric.ball_subset_closedBall.trans hball)
      have hfmean : f c₁ ≤ Real.circleAverage f c₁ ρ :=
        hfmv c₁ (hballρU (Metric.mem_closedBall_self hρ.le)) ρ hρ hballρU
      have hρabs : |ρ| = ρ := abs_of_pos hρ
      have hpmmean : Real.circleAverage (poissonModify f c R) c₁ ρ = poissonModify f c R c₁ := by
        apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
        rw [hρabs]; exact hpmharm.mono hballρ
      -- Circle integrability of `f` and `poissonModify` on the circle.
      have hsphereρU : Metric.sphere c₁ ρ ⊆ U :=
        (Metric.sphere_subset_closedBall).trans hballρU
      have hsphereρcb : Metric.sphere c₁ ρ ⊆ Metric.closedBall c R :=
        (Metric.sphere_subset_closedBall).trans
          (hballρ.trans Metric.ball_subset_closedBall)
      have hfci : CircleIntegrable f c₁ ρ :=
        (hfcU.mono hsphereρU).circleIntegrable hρ.le
      have hpmci : CircleIntegrable (poissonModify f c R) c₁ ρ :=
        (hpmcont.mono hsphereρcb).circleIntegrable hρ.le
      -- `⨍ g = ⨍ f - ⨍ poissonModify`.
      have hgavg : Real.circleAverage g c₁ ρ
          = Real.circleAverage f c₁ ρ - Real.circleAverage (poissonModify f c R) c₁ ρ := by
        rw [hg]; exact Real.circleAverage_fun_sub hfci hpmci
      -- Conclude the sub-mean-value inequality for `g`.
      rw [hg]; simp only
      rw [show Real.circleAverage (fun w => f w - poissonModify f c R w) c₁ ρ
            = Real.circleAverage f c₁ ρ - Real.circleAverage (poissonModify f c R) c₁ ρ from
          Real.circleAverage_fun_sub hfci hpmci, hpmmean]
      linarith [hfmean]
  -- Apply the maximum principle to `g` on the bounded open ball.
  have hgcont : ContinuousOn g (closure (Metric.ball c R)) := by
    rw [closure_ball c hRne]
    apply ContinuousOn.sub (hfcU.mono hball) hpmcont
  have hgfront : ∀ z ∈ frontier (Metric.ball c R), g z ≤ 0 := by
    intro z hz
    rw [frontier_ball c hRne] at hz
    have hnotball : z ∉ Metric.ball c R := by
      rw [Metric.mem_ball, Metric.mem_sphere.1 hz]; exact lt_irrefl _
    rw [hg]; simp only [poissonModify, ite_eq_right hnotball, sub_self, le_refl]
  have hmax := hgsub.le_of_frontier_le Metric.isOpen_ball
    (Metric.isBounded_ball) (by exact hgcont) hgfront
  -- Translate `g ≤ 0` on the ball into `f ≤ poissonModify` on `U`.
  intro z hzU
  by_cases hzball : z ∈ Metric.ball c R
  · have := hmax z hzball
    rw [hg] at this; simp only at this; linarith
  · simp only [poissonModify, ite_eq_right hzball, le_refl]

/-- **Poisson modification is harmonic on the open disk.** Immediate from
`poissonIntegral_harmonicOn` (the modification equals the Poisson integral there, and `f` is
continuous on the boundary circle). -/
theorem poissonModify_harmonicOn {f : ℂ → ℝ} {U : Set ℂ}
    (hf : SubharmonicOn f U) {c : ℂ} {R : ℝ} (hR : 0 < R) (hball : Metric.closedBall c R ⊆ U) :
    InnerProductSpace.HarmonicOnNhd (poissonModify f c R) (Metric.ball c R) := by
  classical
  -- `f` is continuous on the boundary circle.
  have hsphere : Metric.sphere c R ⊆ U :=
    (Metric.sphere_subset_closedBall).trans hball
  have hfsphere : ContinuousOn f (Metric.sphere c R) := hf.1.mono hsphere
  -- The Poisson integral is harmonic on the open ball.
  have hharm : InnerProductSpace.HarmonicOnNhd (poissonIntegral f c R) (Metric.ball c R) :=
    poissonIntegral_harmonicOn f c hR hfsphere
  -- `poissonModify` agrees with `poissonIntegral` on the open ball.
  intro w hw
  have heq : poissonModify f c R =ᶠ[𝓝 w] poissonIntegral f c R := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hw] with z hz
    simp only [poissonModify, ite_eq_left hz]
  rw [InnerProductSpace.harmonicAt_congr_nhds heq]
  exact hharm w hw

/-- **Poisson modification of a subharmonic function is subharmonic.** The lifted function is
continuous (the Poisson integral matches `f` on the boundary circle by
`poissonIntegral_tendsto_boundary`), dominates `f` (`poissonModify_ge`), is harmonic inside the disk
(`poissonModify_harmonicOn`), and retains the sub-mean-value inequality elsewhere. -/
theorem SubharmonicOn.poissonModify {f : ℂ → ℝ} {U : Set ℂ}
    (hf : SubharmonicOn f U) {c : ℂ} {R : ℝ} (hR : 0 < R) (hball : Metric.closedBall c R ⊆ U) :
    SubharmonicOn (poissonModify f c R) U := by
  classical
  obtain ⟨hfcU, hfmv⟩ := hf
  have hRne : R ≠ 0 := ne_of_gt hR
  have hsphere : Metric.sphere c R ⊆ U := (Metric.sphere_subset_closedBall).trans hball
  have hfsphere : ContinuousOn f (Metric.sphere c R) := hfcU.mono hsphere
  set P : ℂ → ℝ := RiemannDynamics.poissonModify f c R with hP
  -- `P` is harmonic on the open ball.
  have hPharm : InnerProductSpace.HarmonicOnNhd P (Metric.ball c R) :=
    poissonModify_harmonicOn ⟨hfcU, hfmv⟩ hR hball
  have hPball : ContinuousOn P (Metric.ball c R) := hPharm.continuousOn
  have hPgef : ∀ z ∈ U, f z ≤ P z := poissonModify_ge ⟨hfcU, hfmv⟩ hR hball
  -- `P = f` outside the open ball.
  have hPoff : ∀ z, z ∉ Metric.ball c R → P z = f z := by
    intro z hz; simp only [hP, RiemannDynamics.poissonModify, ite_eq_right hz]
  -- `P` is continuous on the closed ball (boundary matching via the Poisson boundary limit).
  have hPcb : ContinuousOn P (Metric.closedBall c R) := by
    have hPI : ContinuousOn (poissonIntegral f c R) (Metric.ball c R) :=
      (poissonIntegral_harmonicOn f c hR hfsphere).continuousOn
    have hsplit : Metric.closedBall c R = Metric.ball c R ∪ Metric.sphere c R :=
      Metric.ball_union_sphere.symm
    intro ζ hζ
    rw [Metric.mem_closedBall] at hζ
    rcases lt_or_eq_of_le hζ with hlt | heq
    · have hζball : ζ ∈ Metric.ball c R := Metric.mem_ball.2 hlt
      exact ((hPball ζ hζball).continuousAt
        (Metric.isOpen_ball.mem_nhds hζball)).continuousWithinAt
    · have hζsphere : ζ ∈ Metric.sphere c R := Metric.mem_sphere.2 heq
      have hnotball : ζ ∉ Metric.ball c R := by rw [Metric.mem_ball, heq]; exact lt_irrefl _
      have hPζ : P ζ = f ζ := hPoff ζ hnotball
      rw [hsplit]
      apply ContinuousWithinAt.union
      · have htend : Tendsto (poissonIntegral f c R) (𝓝[Metric.ball c R] ζ) (𝓝 (f ζ)) :=
          poissonIntegral_tendsto_boundary f c hR hfsphere hζsphere
        have heqball : P =ᶠ[𝓝[Metric.ball c R] ζ] poissonIntegral f c R := by
          filter_upwards [self_mem_nhdsWithin] with z hz
          simp only [hP, RiemannDynamics.poissonModify, ite_eq_left hz]
        rw [ContinuousWithinAt, hPζ]
        exact htend.congr' heqball.symm
      · have hcwf : ContinuousWithinAt f (Metric.sphere c R) ζ := hfsphere ζ hζsphere
        apply hcwf.congr (fun z hz => ?_) hPζ
        have : z ∉ Metric.ball c R := by
          rw [Metric.mem_ball, Metric.mem_sphere.1 hz]; exact lt_irrefl _
        simp only [hP, RiemannDynamics.poissonModify, ite_eq_right this]
  -- `P` is continuous on `U`.
  have hPcontU : ContinuousOn P U := by
    intro z hzU
    have hcover : U = Metric.closedBall c R ∪ (U ∩ (Metric.ball c R)ᶜ) := by
      ext x; constructor
      · intro hx
        by_cases hb : x ∈ Metric.ball c R
        · exact Or.inl (Metric.ball_subset_closedBall hb)
        · exact Or.inr ⟨hx, hb⟩
      · rintro (hx | ⟨hx, _⟩)
        · exact hball hx
        · exact hx
    rw [hcover]
    apply ContinuousWithinAt.union
    · -- within the closed ball
      by_cases hzcb : z ∈ Metric.closedBall c R
      · exact hPcb z hzcb
      · -- `z` is outside the closed ball, which is closed, so the within-filter is `⊥`.
        have hbot : 𝓝[Metric.closedBall c R] z = ⊥ := by
          rw [nhdsWithin, inf_principal_eq_bot]
          exact (isClosed_closedBall (x := c) (ε := R)).isOpen_compl.mem_nhds hzcb
        rw [ContinuousWithinAt, hbot]; exact tendsto_bot
    · -- within `U ∩ (ball)ᶜ`, where `P = f`.
      by_cases hzb : z ∈ Metric.ball c R
      · have hbot : 𝓝[U ∩ (Metric.ball c R)ᶜ] z = ⊥ := by
          rw [nhdsWithin, inf_principal_eq_bot]
          apply Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hzb)
          intro x hx; simp only [Set.mem_compl_iff, Set.mem_inter_iff, not_and, not_not]
          intro _; exact hx
        rw [ContinuousWithinAt, hbot]; exact tendsto_bot
      · have hcwf : ContinuousWithinAt f (U ∩ (Metric.ball c R)ᶜ) z :=
          (hfcU.mono Set.inter_subset_left) z ⟨hzU, hzb⟩
        apply hcwf.congr (fun x hx => ?_) (hPoff z hzb)
        exact hPoff x hx.2
  -- Helper: the sub-mean-value inequality for `P` at points outside the open ball.
  have hPsub_off : ∀ p ∈ U, p ∉ Metric.ball c R → ∀ ρ : ℝ, 0 < ρ →
      Metric.closedBall p ρ ⊆ U → P p ≤ Real.circleAverage P p ρ := by
    intro p hpU hpball ρ hρ hballρ
    have hballρU : Metric.closedBall p ρ ⊆ U := hballρ
    have hsphereρU : Metric.sphere p ρ ⊆ U := (Metric.sphere_subset_closedBall).trans hballρU
    have hfci : CircleIntegrable f p ρ := (hfcU.mono hsphereρU).circleIntegrable hρ.le
    have hPci : CircleIntegrable P p ρ := (hPcontU.mono hsphereρU).circleIntegrable hρ.le
    have hρabs : |ρ| = ρ := abs_of_pos hρ
    have hfmean : f p ≤ Real.circleAverage f p ρ :=
      hfmv p hpU ρ hρ hballρU
    have hmono : Real.circleAverage f p ρ ≤ Real.circleAverage P p ρ := by
      apply Real.circleAverage_mono hfci hPci
      intro x hx
      rw [hρabs] at hx
      exact hPgef x (hsphereρU hx)
    have hPp : P p = f p := hPoff p hpball
    rw [hPp]; linarith
  -- A general modification helper: for a function `φ` continuous on `U` and a disk in `U`, its
  -- Poisson modification on the disk is harmonic inside, continuous up to the boundary, and agrees
  -- with `φ` on (and outside) the boundary circle.
  have hmod : ∀ (φ : ℂ → ℝ), ContinuousOn φ U → ∀ (a : ℂ) (ρ : ℝ), 0 < ρ →
      Metric.closedBall a ρ ⊆ U →
      InnerProductSpace.HarmonicOnNhd (RiemannDynamics.poissonModify φ a ρ) (Metric.ball a ρ)
      ∧ ContinuousOn (RiemannDynamics.poissonModify φ a ρ) (Metric.closedBall a ρ)
      ∧ (∀ z, z ∉ Metric.ball a ρ → RiemannDynamics.poissonModify φ a ρ z = φ z) := by
    intro φ hφU a ρ hρ hballρ
    have hρne : ρ ≠ 0 := ne_of_gt hρ
    have hsphereρ : Metric.sphere a ρ ⊆ U := (Metric.sphere_subset_closedBall).trans hballρ
    have hφsphere : ContinuousOn φ (Metric.sphere a ρ) := hφU.mono hsphereρ
    have hQharm : InnerProductSpace.HarmonicOnNhd (poissonIntegral φ a ρ) (Metric.ball a ρ) :=
      poissonIntegral_harmonicOn φ a hρ hφsphere
    have hQball : ContinuousOn (poissonIntegral φ a ρ) (Metric.ball a ρ) := hQharm.continuousOn
    have hoff : ∀ z, z ∉ Metric.ball a ρ → RiemannDynamics.poissonModify φ a ρ z = φ z := by
      intro z hz; simp only [RiemannDynamics.poissonModify, ite_eq_right hz]
    refine ⟨?_, ?_, hoff⟩
    · intro w hw
      have heqw : RiemannDynamics.poissonModify φ a ρ =ᶠ[𝓝 w] poissonIntegral φ a ρ := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hw] with z hz
        simp only [RiemannDynamics.poissonModify, ite_eq_left hz]
      rw [InnerProductSpace.harmonicAt_congr_nhds heqw]
      exact hQharm w hw
    · have hsplit : Metric.closedBall a ρ = Metric.ball a ρ ∪ Metric.sphere a ρ :=
        Metric.ball_union_sphere.symm
      intro ζ hζ
      rw [Metric.mem_closedBall] at hζ
      rcases lt_or_eq_of_le hζ with hlt | heq
      · have hζball : ζ ∈ Metric.ball a ρ := Metric.mem_ball.2 hlt
        have heqf : RiemannDynamics.poissonModify φ a ρ =ᶠ[𝓝 ζ] poissonIntegral φ a ρ := by
          filter_upwards [Metric.isOpen_ball.mem_nhds hζball] with z hz
          simp only [RiemannDynamics.poissonModify, ite_eq_left hz]
        have hca : ContinuousAt (poissonIntegral φ a ρ) ζ :=
          (hQball ζ hζball).continuousAt (Metric.isOpen_ball.mem_nhds hζball)
        exact (hca.congr heqf.symm).continuousWithinAt
      · have hζsphere : ζ ∈ Metric.sphere a ρ := Metric.mem_sphere.2 heq
        have hnotball : ζ ∉ Metric.ball a ρ := by rw [Metric.mem_ball, heq]; exact lt_irrefl _
        have hPζ : RiemannDynamics.poissonModify φ a ρ ζ = φ ζ := hoff ζ hnotball
        rw [hsplit]
        apply ContinuousWithinAt.union
        · have htend : Tendsto (poissonIntegral φ a ρ) (𝓝[Metric.ball a ρ] ζ) (𝓝 (φ ζ)) :=
            poissonIntegral_tendsto_boundary φ a hρ hφsphere hζsphere
          have heqball : RiemannDynamics.poissonModify φ a ρ
              =ᶠ[𝓝[Metric.ball a ρ] ζ] poissonIntegral φ a ρ := by
            filter_upwards [self_mem_nhdsWithin] with z hz
            simp only [RiemannDynamics.poissonModify, ite_eq_left hz]
          rw [ContinuousWithinAt, hPζ]
          exact htend.congr' heqball.symm
        · have hcwf : ContinuousWithinAt φ (Metric.sphere a ρ) ζ := hφsphere ζ hζsphere
          apply hcwf.congr (fun z hz => ?_) hPζ
          have : z ∉ Metric.ball a ρ := by
            rw [Metric.mem_ball, Metric.mem_sphere.1 hz]; exact lt_irrefl _
          simp only [RiemannDynamics.poissonModify, ite_eq_right this]
  refine ⟨hPcontU, ?_⟩
  intro c₀ hc₀ r hr hballr
  by_cases hc₀ball : c₀ ∈ Metric.ball c R
  · -- Crossing-circle case: compare `P` with its Poisson modification `H` on the disk.
    have hrne : r ≠ 0 := ne_of_gt hr
    have hballrU : Metric.closedBall c₀ r ⊆ U := hballr
    have hsphererU : Metric.sphere c₀ r ⊆ U := (Metric.sphere_subset_closedBall).trans hballrU
    obtain ⟨hHharm, hHcb, hHoff⟩ := hmod P hPcontU c₀ r hr hballr
    set H : ℂ → ℝ := RiemannDynamics.poissonModify P c₀ r with hH
    -- `H = P` on (and outside) the boundary circle.
    have hHeqP_off : ∀ z, z ∉ Metric.ball c₀ r → H z = P z := hHoff
    -- `H` is `HarmonicContOnCl` on `ball c₀ r`, hence its circle average equals `H c₀`.
    have hHcontcl : ContinuousOn H (closure (Metric.ball c₀ r)) := by
      rw [closure_ball c₀ hrne]; exact hHcb
    have hHmean : Real.circleAverage H c₀ r = H c₀ := by
      apply InnerProductSpace.HarmonicContOnCl.circleAverage_eq
      refine ⟨?_, ?_⟩
      · rw [abs_of_pos hr]; exact hHharm
      · rw [abs_of_pos hr]; exact hHcontcl
    -- `⨍ H = ⨍ P` since `H = P` on the circle.
    have hHavgP : Real.circleAverage H c₀ r = Real.circleAverage P c₀ r := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hr] at hz
      have : z ∉ Metric.ball c₀ r := by
        rw [Metric.mem_ball, Metric.mem_sphere.1 hz]; exact lt_irrefl _
      exact hHeqP_off z this
    -- Step 1: `f ≤ H` on the closed disk (`f - H` subharmonic, `≤ 0` on the circle).
    have hfleH : ∀ z ∈ Metric.closedBall c₀ r, f z ≤ H z := by
      set w : ℂ → ℝ := fun z => f z - H z with hw
      have hwsub : SubharmonicOn w (Metric.ball c₀ r) := by
        refine ⟨ContinuousOn.sub (hfcU.mono (Metric.ball_subset_closedBall.trans hballrU))
          (hHcb.mono Metric.ball_subset_closedBall), ?_⟩
        intro p hp ρ hρ hballρ
        have hballρU : Metric.closedBall p ρ ⊆ U :=
          hballρ.trans (Metric.ball_subset_closedBall.trans hballrU)
        have hsphereρU : Metric.sphere p ρ ⊆ U := Metric.sphere_subset_closedBall.trans hballρU
        have hρabs : |ρ| = ρ := abs_of_pos hρ
        have hfmean : f p ≤ Real.circleAverage f p ρ :=
          hfmv p (hballρU (Metric.mem_closedBall_self hρ.le)) ρ hρ hballρU
        have hHmean' : Real.circleAverage H p ρ = H p :=
          InnerProductSpace.HarmonicOnNhd.circleAverage_eq (by rw [hρabs]; exact hHharm.mono hballρ)
        have hfci : CircleIntegrable f p ρ := (hfcU.mono hsphereρU).circleIntegrable hρ.le
        have hHci : CircleIntegrable H p ρ :=
          (hHcb.mono ((Metric.sphere_subset_closedBall).trans
            (hballρ.trans Metric.ball_subset_closedBall))).circleIntegrable hρ.le
        rw [hw, Real.circleAverage_fun_sub hfci hHci, hHmean']
        simp only; linarith
      have hwcl : ContinuousOn w (closure (Metric.ball c₀ r)) := by
        rw [closure_ball c₀ hrne]
        exact ContinuousOn.sub (hfcU.mono hballrU) hHcb
      have hwfront : ∀ z ∈ frontier (Metric.ball c₀ r), w z ≤ 0 := by
        intro z hz
        rw [frontier_ball c₀ hrne] at hz
        have hznb : z ∉ Metric.ball c₀ r := by
          rw [Metric.mem_ball, Metric.mem_sphere.1 hz]; exact lt_irrefl _
        rw [hw]; simp only
        have hPz : H z = P z := hHeqP_off z hznb
        rw [hPz]; linarith [hPgef z (hballrU (Metric.sphere_subset_closedBall hz))]
      have hwle := hwsub.le_of_frontier_le Metric.isOpen_ball Metric.isBounded_ball hwcl hwfront
      intro z hz
      rw [Metric.mem_closedBall] at hz
      rcases lt_or_eq_of_le hz with hlt | heq
      · have := hwle z (Metric.mem_ball.2 hlt); rw [hw] at this; simp only at this; linarith
      · have hznb : z ∉ Metric.ball c₀ r := by rw [Metric.mem_ball, heq]; exact lt_irrefl _
        rw [hHeqP_off z hznb]
        exact hPgef z (hballrU (Metric.mem_closedBall.2 hz))
    -- Step 2: `P ≤ H` on `W = ball c R ∩ ball c₀ r` (harmonic difference, `≤ 0` on its frontier).
    set W : Set ℂ := Metric.ball c R ∩ Metric.ball c₀ r with hW
    have hWopen : IsOpen W := Metric.isOpen_ball.inter Metric.isOpen_ball
    have hWbdd : Bornology.IsBounded W :=
      Metric.isBounded_ball.subset Set.inter_subset_left
    have hWclsub : closure W ⊆ Metric.closedBall c R ∩ Metric.closedBall c₀ r := by
      apply (closure_inter_subset_inter_closure _ _).trans
      rw [closure_ball c hRne, closure_ball c₀ hrne]
    set v : ℂ → ℝ := fun z => P z - H z with hv
    have hvharm : InnerProductSpace.HarmonicOnNhd v W := by
      intro x hx
      exact (hPharm x hx.1).sub (hHharm x hx.2)
    have hvsub : SubharmonicOn v W := HarmonicOnNhd.subharmonicOn hvharm
    have hvcl : ContinuousOn v (closure W) := by
      apply ContinuousOn.sub
      · exact hPcontU.mono (hWclsub.trans (Set.inter_subset_left.trans hball))
      · exact hHcb.mono (hWclsub.trans Set.inter_subset_right)
    have hvfront : ∀ z ∈ frontier W, v z ≤ 0 := by
      intro z hz
      have hzcl : z ∈ closure W := frontier_subset_closure hz
      have hznotW : z ∉ W := by
        have := hz.2; rwa [hWopen.interior_eq] at this
      obtain ⟨hzcR, hzcr⟩ := hWclsub hzcl
      rw [hv]; simp only
      by_cases hzb : z ∈ Metric.ball c R
      · -- then `z ∉ ball c₀ r`, so `z ∈ sphere c₀ r` and `H z = P z`.
        have hznotr : z ∉ Metric.ball c₀ r := fun h => hznotW ⟨hzb, h⟩
        rw [hHeqP_off z hznotr]; linarith
      · -- then `z ∈ sphere c R`, so `P z = f z ≤ H z`.
        have hzsphere : z ∈ Metric.sphere c R := by
          rw [Metric.mem_sphere]
          rcases lt_or_eq_of_le (Metric.mem_closedBall.1 hzcR) with h | h
          · exact absurd (Metric.mem_ball.2 h) hzb
          · exact h
        have hPz : P z = f z := hPoff z hzb
        rw [hPz]
        linarith [hfleH z hzcr]
    have hvle := hvsub.le_of_frontier_le hWopen hWbdd hvcl hvfront
    have hc₀W : c₀ ∈ W := ⟨hc₀ball, Metric.mem_ball_self hr⟩
    have hvc₀ : v c₀ ≤ 0 := hvle c₀ hc₀W
    rw [hv] at hvc₀; simp only at hvc₀
    -- Conclude `P c₀ ≤ ⨍ P`.
    calc P c₀ ≤ H c₀ := by linarith
      _ = Real.circleAverage H c₀ r := hHmean.symm
      _ = Real.circleAverage P c₀ r := hHavgP
  · exact hPsub_off c₀ hc₀ hc₀ball r hr hballr

/-- **Subharmonicity from arbitrarily small circles.** A continuous function on an open set that
satisfies the sub-mean-value inequality on all sufficiently small circles at each point satisfies it
on every circle whose closed disk lies in the set: comparison with the harmonic (Poisson)
modification on the closed disk reduces the global inequality to the local one through the maximum
principle, which itself consumes only one small circle per point. -/
theorem subharmonicOn_of_locally {f : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContinuousOn f U)
    (hloc : ∀ c ∈ U, ∃ r₀ > 0, ∀ r : ℝ, 0 < r → r < r₀ → Metric.closedBall c r ⊆ U →
      f c ≤ Real.circleAverage f c r) :
    SubharmonicOn f U := by
  classical
  have _ := hU
  refine ⟨hf, ?_⟩
  intro c _ r hr hball
  have hrne : r ≠ 0 := ne_of_gt hr
  have hsphere : Metric.sphere c r ⊆ U := (Metric.sphere_subset_closedBall).trans hball
  have hfsphere : ContinuousOn f (Metric.sphere c r) := hf.mono hsphere
  -- The harmonic (Poisson) modification `P` of `f` on the disk.
  set P : ℂ → ℝ := poissonModify f c r with hP
  have hPoff : ∀ z, z ∉ Metric.ball c r → P z = f z := by
    intro z hz; simp only [hP, poissonModify, ite_eq_right hz]
  have hQharm : InnerProductSpace.HarmonicOnNhd (poissonIntegral f c r) (Metric.ball c r) :=
    poissonIntegral_harmonicOn f c hr hfsphere
  -- `P` is harmonic on the open ball.
  have hPharm : InnerProductSpace.HarmonicOnNhd P (Metric.ball c r) := by
    intro w hw
    have heqw : P =ᶠ[𝓝 w] poissonIntegral f c r := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hw] with z hz
      simp only [hP, poissonModify, ite_eq_left hz]
    rw [InnerProductSpace.harmonicAt_congr_nhds heqw]
    exact hQharm w hw
  -- `P` is continuous on the closed ball (Poisson boundary limit matches `f` on the circle).
  have hPcb : ContinuousOn P (Metric.closedBall c r) := by
    have hQball : ContinuousOn (poissonIntegral f c r) (Metric.ball c r) := hQharm.continuousOn
    have hsplit : Metric.closedBall c r = Metric.ball c r ∪ Metric.sphere c r :=
      Metric.ball_union_sphere.symm
    intro ζ hζ
    rw [Metric.mem_closedBall] at hζ
    rcases lt_or_eq_of_le hζ with hlt | heq
    · have hζball : ζ ∈ Metric.ball c r := Metric.mem_ball.2 hlt
      have heqf : P =ᶠ[𝓝 ζ] poissonIntegral f c r := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hζball] with z hz
        simp only [hP, poissonModify, ite_eq_left hz]
      have hca : ContinuousAt (poissonIntegral f c r) ζ :=
        (hQball ζ hζball).continuousAt (Metric.isOpen_ball.mem_nhds hζball)
      exact (hca.congr heqf.symm).continuousWithinAt
    · have hζsphere : ζ ∈ Metric.sphere c r := Metric.mem_sphere.2 heq
      have hnotball : ζ ∉ Metric.ball c r := by rw [Metric.mem_ball, heq]; exact lt_irrefl _
      have hPζ : P ζ = f ζ := hPoff ζ hnotball
      rw [hsplit]
      apply ContinuousWithinAt.union
      · have htend : Tendsto (poissonIntegral f c r) (𝓝[Metric.ball c r] ζ) (𝓝 (f ζ)) :=
          poissonIntegral_tendsto_boundary f c hr hfsphere hζsphere
        have heqball : P =ᶠ[𝓝[Metric.ball c r] ζ] poissonIntegral f c r := by
          filter_upwards [self_mem_nhdsWithin] with z hz
          simp only [hP, poissonModify, ite_eq_left hz]
        rw [ContinuousWithinAt, hPζ]
        exact htend.congr' heqball.symm
      · have hcwf : ContinuousWithinAt f (Metric.sphere c r) ζ := hfsphere ζ hζsphere
        apply hcwf.congr (fun z hz => ?_) hPζ
        have : z ∉ Metric.ball c r := by
          rw [Metric.mem_ball, Metric.mem_sphere.1 hz]; exact lt_irrefl _
        simp only [hP, poissonModify, ite_eq_right this]
  -- The difference `g = f - P` vanishes on the circle and obeys the small-circle inequality.
  set g : ℂ → ℝ := fun z => f z - P z with hg
  have hgcont : ContinuousOn g (Metric.closedBall c r) := by
    apply ContinuousOn.sub (hf.mono hball) hPcb
  -- Maximum principle from small circles: `g ≤ 0` on the open ball.
  have hgle : ∀ z ∈ Metric.ball c r, g z ≤ 0 := by
    intro c₁ hc₁
    by_contra hcon
    rw [not_le] at hcon
    -- The strictly subharmonic perturbation `q z = ‖z - c₁‖²` (with `q c₁ = 0`).
    set q : ℂ → ℝ := fun z => ‖z - c₁‖ ^ 2 with hq
    -- Exact circle average of `q`: `⨍_{sphere a ρ} q = ‖a - c₁‖² + ρ²`.
    have hqavg : ∀ (a : ℂ) (ρ : ℝ),
        Real.circleAverage q a ρ = ‖a - c₁‖ ^ 2 + ρ ^ 2 := by
      intro a ρ
      have hcm : ∀ θ : ℝ, ‖circleMap a ρ θ - c₁‖ ^ 2
          = (‖a - c₁‖ ^ 2 + ρ ^ 2) + 2 * ρ * (a - c₁).re * Real.cos θ
            + 2 * ρ * (a - c₁).im * Real.sin θ := by
        intro θ
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        simp only [circleMap, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
          Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
        nlinarith [Real.sin_sq_add_cos_sq θ]
      rw [Real.circleAverage_def]
      have hinteq : (∫ θ in (0 : ℝ)..(2 * π), q (circleMap a ρ θ))
          = ∫ θ in (0 : ℝ)..(2 * π), ((‖a - c₁‖ ^ 2 + ρ ^ 2)
              + 2 * ρ * (a - c₁).re * Real.cos θ + 2 * ρ * (a - c₁).im * Real.sin θ) :=
        intervalIntegral.integral_congr (fun θ _ => hcm θ)
      rw [hinteq]
      have hc1 : IntervalIntegrable (fun _ : ℝ => ‖a - c₁‖ ^ 2 + ρ ^ 2) volume 0 (2 * π) :=
        continuous_const.intervalIntegrable _ _
      have hc2 : IntervalIntegrable (fun θ : ℝ => 2 * ρ * (a - c₁).re * Real.cos θ)
          volume 0 (2 * π) := by
        have : Continuous fun θ : ℝ => 2 * ρ * (a - c₁).re * Real.cos θ := by fun_prop
        exact this.intervalIntegrable _ _
      have hc3 : IntervalIntegrable (fun θ : ℝ => 2 * ρ * (a - c₁).im * Real.sin θ)
          volume 0 (2 * π) := by
        have : Continuous fun θ : ℝ => 2 * ρ * (a - c₁).im * Real.sin θ := by fun_prop
        exact this.intervalIntegrable _ _
      rw [intervalIntegral.integral_add (hc1.add hc2) hc3,
        intervalIntegral.integral_add hc1 hc2, intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_cos, integral_sin]
      simp only [Real.sin_zero, Real.sin_two_pi, Real.cos_zero, Real.cos_two_pi, smul_eq_mul]
      have hpi : (2 * π) ≠ 0 := by positivity
      field_simp
      ring
    have hqcont : Continuous q := by rw [hq]; fun_prop
    -- A uniform bound `q ≤ C` on the compact closed disk.
    have hKcompact : IsCompact (Metric.closedBall c r) := isCompact_closedBall c r
    obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn (f := q) hqcont.continuousOn
    have hc₁K : c₁ ∈ Metric.closedBall c r := Metric.ball_subset_closedBall hc₁
    have hC0 : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC c₁ hc₁K)
    have hqle : ∀ z ∈ Metric.closedBall c r, q z ≤ C := fun z hz => le_trans (le_abs_self _)
      (by simpa [Real.norm_eq_abs] using hC z hz)
    -- Choose `ε > 0` so small that `ε C < g c₁`.
    set ε : ℝ := g c₁ / (C + 1) with hε
    have hεpos : 0 < ε := by
      rw [hε]; apply div_pos (by linarith [hcon]) (by positivity)
    have hperturb : ε * C < g c₁ := by
      rw [hε]
      have hCC : C / (C + 1) < 1 := by
        rw [div_lt_one (by positivity)]; linarith
      have : g c₁ / (C + 1) * C = g c₁ * (C / (C + 1)) := by ring
      rw [this]
      nlinarith [hcon, hCC]
    -- The perturbed function `G = g + ε q` attains its maximum on the closed disk at some `p`.
    set G : ℂ → ℝ := fun z => g z + ε * q z with hG
    have hGcont : ContinuousOn G (Metric.closedBall c r) := by
      apply ContinuousOn.add hgcont
      exact continuousOn_const.mul hqcont.continuousOn
    obtain ⟨p, hpK, hpmax⟩ := hKcompact.exists_isMaxOn ⟨c₁, hc₁K⟩ hGcont
    -- The maximum point cannot lie in the open ball: `hloc` supplies a small circle there.
    have hpV : p ∉ Metric.ball c r := by
      intro hpball
      obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.1 Metric.isOpen_ball p hpball
      obtain ⟨r₀, hr₀pos, hsmv⟩ := hloc p (hball (Metric.ball_subset_closedBall hpball))
      set ρ : ℝ := min (δ / 2) (r₀ / 2) with hρ
      have hρpos : 0 < ρ := by
        rw [hρ]; exact lt_min (by linarith) (by linarith)
      have hρltr₀ : ρ < r₀ := by
        rw [hρ]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hρabs : |ρ| = ρ := abs_of_pos hρpos
      have hballρ : Metric.closedBall p ρ ⊆ Metric.ball c r := by
        intro z hz
        apply hδsub
        rw [Metric.mem_ball]
        rw [Metric.mem_closedBall] at hz
        have hρδ : ρ < δ := by
          rw [hρ]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
        linarith
      have hballρU : Metric.closedBall p ρ ⊆ U :=
        hballρ.trans (Metric.ball_subset_closedBall.trans hball)
      have hsphereρ : Metric.sphere p ρ ⊆ Metric.closedBall c r :=
        (Metric.sphere_subset_closedBall).trans (hballρ.trans Metric.ball_subset_closedBall)
      -- Circle-integrability on `sphere p ρ`.
      have hfci : CircleIntegrable f p ρ :=
        (hf.mono ((Metric.sphere_subset_closedBall).trans hballρU)).circleIntegrable hρpos.le
      have hPci : CircleIntegrable P p ρ := (hPcb.mono hsphereρ).circleIntegrable hρpos.le
      have hgci : CircleIntegrable g p ρ := (hgcont.mono hsphereρ).circleIntegrable hρpos.le
      have hGci : CircleIntegrable G p ρ := (hGcont.mono hsphereρ).circleIntegrable hρpos.le
      -- Sub-mean-value for `g` on this circle: `f` by `hloc`, `P` by harmonicity.
      have hfmean : f p ≤ Real.circleAverage f p ρ := hsmv ρ hρpos hρltr₀ hballρU
      have hPmeanρ : Real.circleAverage P p ρ = P p :=
        InnerProductSpace.HarmonicOnNhd.circleAverage_eq (by rw [hρabs]; exact hPharm.mono hballρ)
      have hgmean : g p ≤ Real.circleAverage g p ρ := by
        rw [hg]; simp only
        rw [show Real.circleAverage (fun z => f z - P z) p ρ
              = Real.circleAverage f p ρ - Real.circleAverage P p ρ from
            Real.circleAverage_fun_sub hfci hPci, hPmeanρ]
        linarith [hfmean]
      have hqmean : Real.circleAverage q p ρ = q p + ρ ^ 2 := by
        rw [hqavg p ρ, hq]
      -- Strict sub-mean-value inequality for `G` at `p`.
      have hGavg : Real.circleAverage G p ρ
          = Real.circleAverage g p ρ + ε * (q p + ρ ^ 2) := by
        rw [hG]
        rw [show (fun z => g z + ε * q z) = g + (fun z => ε * q z) from rfl]
        rw [Real.circleAverage_add hgci (by
          apply (((continuousOn_const).mul hqcont.continuousOn).circleIntegrable hρpos.le))]
        rw [show (fun z => ε * q z) = (fun z => ε • q z) from funext fun z => by
          simp [smul_eq_mul]]
        rw [Real.circleAverage_fun_smul, hqmean, smul_eq_mul]
      have hGstrict : G p < Real.circleAverage G p ρ := by
        rw [hGavg, hG]
        have : ε * q p < ε * (q p + ρ ^ 2) := by
          apply mul_lt_mul_of_pos_left _ hεpos
          nlinarith [hρpos]
        simp only
        linarith [hgmean]
      -- But `p` is a maximum of `G`, so `⨍ G ≤ G p`.
      have hGmax_avg : Real.circleAverage G p ρ ≤ G p := by
        apply Real.circleAverage_mono_on_of_le_circle hGci
        intro x hx
        have hxK : x ∈ Metric.closedBall c r := hsphereρ (by rwa [hρabs] at hx)
        exact hpmax hxK
      linarith [hGstrict, hGmax_avg]
    -- Hence `p` lies on the circle, where `g p = 0`; the maximum forces `g c₁ ≤ ε C`.
    have hgp : g p = 0 := by
      rw [hg]; simp only [hPoff p hpV, sub_self]
    have hmaxc₁ : G c₁ ≤ G p := hpmax hc₁K
    have hGc₁ : G c₁ = g c₁ := by
      rw [hG]; simp only [hq, sub_self, norm_zero]; ring
    have hGp : G p ≤ ε * C := by
      rw [hG]; simp only
      have hqpC : q p ≤ C := hqle p hpK
      linarith [hgp, mul_le_mul_of_nonneg_left hqpC hεpos.le]
    rw [hGc₁] at hmaxc₁
    linarith [hmaxc₁, hGp, hperturb]
  -- Conclude via the mean value of the harmonic modification at the full radius.
  have hfcP : f c ≤ P c := by
    have := hgle c (Metric.mem_ball_self hr)
    rw [hg] at this; simp only at this; linarith
  have hPcontcl : ContinuousOn P (closure (Metric.ball c r)) := by
    rw [closure_ball c hrne]; exact hPcb
  have hPmean : Real.circleAverage P c r = P c := by
    apply InnerProductSpace.HarmonicContOnCl.circleAverage_eq
    refine ⟨?_, ?_⟩
    · rw [abs_of_pos hr]; exact hPharm
    · rw [abs_of_pos hr]; exact hPcontcl
  have hPavgf : Real.circleAverage P c r = Real.circleAverage f c r := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    rw [abs_of_pos hr] at hz
    have : z ∉ Metric.ball c r := by
      rw [Metric.mem_ball, Metric.mem_sphere.1 hz]; exact lt_irrefl _
    exact hPoff z this
  calc f c ≤ P c := hfcP
    _ = Real.circleAverage P c r := hPmean.symm
    _ = Real.circleAverage f c r := hPavgf

/-- **Subharmonicity of the extension by zero.** For `u` harmonic and nonnegative on `V ∩ W`, if
the extension of `u` by `0` off `V` is continuous on the open set `W`, then that extension is
subharmonic on `W`. At a centre in `V` small circle averages agree with those of `u` and the
mean-value equality applies; at a centre outside `V` the extension vanishes while its circle
averages are nonnegative. -/
theorem subharmonicOn_indicator_of_harmonicOnNhd {u : ℂ → ℝ} {V W : Set ℂ}
    (hV : IsOpen V) (hW : IsOpen W)
    (hu : InnerProductSpace.HarmonicOnNhd u (V ∩ W))
    (hu0 : ∀ z ∈ V ∩ W, 0 ≤ u z)
    (hcont : ContinuousOn (Set.indicator V u) W) :
    SubharmonicOn (Set.indicator V u) W := by
  apply subharmonicOn_of_locally hW hcont
  intro c hc
  by_cases hcV : c ∈ V
  · -- Centre in `V`: small closed disks lie in `V ∩ W`, where the indicator equals `u` and the
    -- mean-value equality for the harmonic function `u` applies.
    obtain ⟨r₀, hr₀pos, hr₀sub⟩ := Metric.isOpen_iff.1 (hV.inter hW) c ⟨hcV, hc⟩
    refine ⟨r₀, hr₀pos, fun r hr hrlt _ => ?_⟩
    have hball : Metric.closedBall c r ⊆ V ∩ W :=
      (Metric.closedBall_subset_ball hrlt).trans hr₀sub
    have habs : |r| = r := abs_of_pos hr
    have havg : Real.circleAverage (Set.indicator V u) c r = Real.circleAverage u c r := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [habs] at hz
      exact Set.indicator_of_mem (hball (Metric.sphere_subset_closedBall hz)).1 u
    have hmean : Real.circleAverage u c r = u c :=
      InnerProductSpace.HarmonicOnNhd.circleAverage_eq (by rw [habs]; exact hu.mono hball)
    have heq : Set.indicator V u c = Real.circleAverage (Set.indicator V u) c r := by
      rw [Set.indicator_of_mem hcV, havg, hmean]
    exact heq.le
  · -- Centre off `V`: the indicator vanishes at `c` while its circle averages are nonnegative,
    -- since on each admissible circle the integrand is `u ≥ 0` on `V ∩ W` and `0` off `V`.
    refine ⟨1, one_pos, fun r hr _ hball => ?_⟩
    rw [Set.indicator_of_notMem hcV]
    apply Real.circleAverage_nonneg_of_nonneg
    intro z hz
    rw [abs_of_pos hr] at hz
    have hzW : z ∈ W := hball (Metric.sphere_subset_closedBall hz)
    by_cases hzV : z ∈ V
    · rw [Set.indicator_of_mem hzV]; exact hu0 z ⟨hzV, hzW⟩
    · rw [Set.indicator_of_notMem hzV]

end RiemannDynamics
