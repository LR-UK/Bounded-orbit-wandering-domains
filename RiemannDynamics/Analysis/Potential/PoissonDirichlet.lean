/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# The Dirichlet problem on a disk via the Poisson integral

The **Poisson integral** of boundary data `g` on the circle `{|z - c| = R}` is the circle average of
`g` weighted by the Poisson kernel:

`poissonIntegral g c R w = ⨍_{|z-c|=R} poissonKernel c w z · g z`.

It solves the **Dirichlet problem on the disk**: the result is harmonic on the open ball `ball c R`
and attains the boundary values `g` continuously at every point of the circle where `g` is
continuous. Mathlib provides the Poisson kernel (`poissonKernel`, as the real part of the
Herglotz–Riesz kernel) and the *reproducing* identity that a harmonic function equals its own
Poisson integral (`HarmonicOnNhd.circleAverage_poissonKernel_smul`); here we establish the
*converse* — that
the Poisson integral of arbitrary continuous boundary data is itself harmonic and continuous up to
the boundary.

This is the bedrock of **Perron's method**: the Dirichlet solution on a disk is the local
modification operator used to build the harmonic potential of a general ring domain (whence the
conformal modulus and conjugate-modulus reciprocity).

## Main definitions

* `poissonIntegral g c R` — the Poisson integral of boundary data `g` on the circle of radius `R`
  about `c`.

## Main statements

* `poissonIntegral_harmonicOn` — the Poisson integral is harmonic on the open ball;
* `poissonIntegral_tendsto_boundary` — at a boundary point where `g` is continuous, the Poisson
  integral converges to `g`.
-/

open MeasureTheory Filter Metric Topology
open scoped Real Topology

namespace RiemannDynamics

/-- The **Poisson integral** of boundary data `g : ℂ → ℝ` on the circle `{|z - c| = R}`, evaluated
at an interior point `w`: the circle average over the boundary circle of `g` weighted by the Poisson
kernel `poissonKernel c w`. For harmonic `g` this reproduces `g` on the open ball; for arbitrary
continuous `g` it is the Dirichlet solution with boundary data `g`. -/
noncomputable def poissonIntegral (g : ℂ → ℝ) (c : ℂ) (R : ℝ) (w : ℂ) : ℝ :=
  Real.circleAverage (fun z => poissonKernel c w z * g z) c R

/-- **Interior harmonicity of the Poisson integral (the Dirichlet problem on a disk).** For boundary
data `g` continuous on the circle `{|z - c| = R}`, the Poisson integral `poissonIntegral g c R` is
harmonic on the open ball `ball c R`. The Poisson kernel `poissonKernel c w z` is harmonic in the
interior variable `w` (it is the real part of the holomorphic Herglotz–Riesz kernel), and
harmonicity passes through the boundary circle average. -/
theorem poissonIntegral_harmonicOn (g : ℂ → ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hg : ContinuousOn g (Metric.sphere c R)) :
    InnerProductSpace.HarmonicOnNhd (poissonIntegral g c R) (Metric.ball c R) := by
  classical
  -- The complex-valued Herglotz integral; its real part is the Poisson integral.
  set F : ℂ → ℂ := fun w =>
    Real.circleAverage (fun z => herglotzRieszKernel c w z * (g z : ℂ)) c R with hF
  -- `g` is bounded on the (compact) boundary circle.
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z ∈ Metric.sphere c R, ‖(g z : ℂ)‖ ≤ M :=
    (isCompact_sphere c R).exists_bound_of_continuousOn
      (f := fun z => (g z : ℂ)) (by fun_prop)
  -- On `sphere c R`, for `w ∈ ball c R` the denominator `(z-c)-(w-c) = z-w` never vanishes.
  have hden : ∀ {w : ℂ}, w ∈ Metric.ball c R → ∀ θ : ℝ,
      (circleMap c R θ - c) - (w - c) ≠ 0 := by
    intro w hw θ
    have hz : ‖circleMap c R θ - c‖ = R := by
      rw [circleMap_sub_center]; simp [norm_circleMap_zero, abs_of_pos hR]
    have hwlt : ‖w - c‖ < R := by simpa [dist_eq_norm] using hw
    intro hcontra
    have : circleMap c R θ - c = w - c := by linear_combination (norm := ring_nf) hcontra
    rw [this] at hz
    exact (lt_irrefl R) (hz ▸ hwlt)
  -- The integrand `z ↦ herglotz · g` is continuous on the circle (for `w` inside the ball).
  have hcont : ∀ {w : ℂ}, w ∈ Metric.ball c R →
      ContinuousOn (fun z => herglotzRieszKernel c w z * (g z : ℂ)) (Metric.sphere c R) := by
    intro w hw
    have hk : ContinuousOn (herglotzRieszKernel c w) (Metric.sphere c R) := by
      rw [herglotzRieszKernel_fun_def]
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro z hz
      have hzc : ‖z - c‖ = R := by simpa [dist_eq_norm] using hz
      have hwlt : ‖w - c‖ < R := by simpa [dist_eq_norm] using hw
      intro hcontra
      have : z - c = w - c := by linear_combination (norm := ring_nf) hcontra
      rw [this] at hzc; exact (lt_irrefl R) (hzc ▸ hwlt)
    exact hk.mul (by fun_prop)
  -- Pointwise: the real part of `F` is the Poisson integral, on `ball c R`.
  have hreF : ∀ w ∈ Metric.ball c R, (F w).re = poissonIntegral g c R w := by
    intro w hw
    have hci : CircleIntegrable (fun z => herglotzRieszKernel c w z * (g z : ℂ)) c R :=
      (hcont hw).circleIntegrable hR.le
    have hcomm := Complex.reCLM.circleAverage_comp_comm hci
    rw [hF]
    change (Real.circleAverage (fun z => herglotzRieszKernel c w z * (g z : ℂ)) c R).re = _
    rw [← Complex.reCLM_apply, ← hcomm, poissonIntegral]
    apply Real.circleAverage_congr_sphere
    intro z hz
    simp only [Function.comp_apply, Complex.reCLM_apply, poissonKernel_eq_re_herglotzRieszKernel,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  -- `F` is holomorphic on the ball: differentiate under the integral sign.
  have hFdiff : DifferentiableOn ℂ F (Metric.ball c R) := by
    intro w₀ hw₀
    -- Choose a closed sub-ball around `w₀` strictly inside `ball c R`.
    obtain ⟨ρ, hρpos, hρsub⟩ : ∃ ρ > 0, Metric.closedBall w₀ ρ ⊆ Metric.ball c R := by
      obtain ⟨ρ, hρpos, hρsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1
        (Metric.isOpen_ball.mem_nhds hw₀)
      exact ⟨ρ, hρpos, hρsub⟩
    set s : Set ℂ := Metric.ball w₀ ρ with hs
    have hsnhds : s ∈ 𝓝 w₀ := Metric.ball_mem_nhds w₀ hρpos
    have hssub : s ⊆ Metric.ball c R :=
      (Metric.ball_subset_closedBall).trans hρsub
    -- Uniform radius bound `r₀ < R` on the closed sub-ball.
    obtain ⟨wm, hwm, hwmax⟩ := (isCompact_closedBall w₀ ρ).exists_isMaxOn
      (Metric.nonempty_closedBall.2 hρpos.le) (f := fun w => ‖w - c‖) (by fun_prop)
    set r₀ : ℝ := ‖wm - c‖ with hr₀
    have hr₀lt : r₀ < R := by
      have := hρsub hwm; simpa [r₀, dist_eq_norm] using this
    -- For each `w ∈ s`, `‖w - c‖ ≤ r₀`.
    have hwle : ∀ w ∈ s, ‖w - c‖ ≤ r₀ :=
      fun w hw => hwmax (Metric.ball_subset_closedBall hw)
    -- Lower bound on the denominator, uniform over `w ∈ s` and `θ`.
    have hdenlb : ∀ w ∈ s, ∀ θ : ℝ,
        R - r₀ ≤ ‖(circleMap c R θ - c) - (w - c)‖ := by
      intro w hw θ
      have hz : ‖circleMap c R θ - c‖ = R := by
        rw [circleMap_sub_center]; simp [norm_circleMap_zero, abs_of_pos hR]
      calc R - r₀ ≤ R - ‖w - c‖ := by linarith [hwle w hw]
        _ = ‖circleMap c R θ - c‖ - ‖w - c‖ := by rw [hz]
        _ ≤ ‖(circleMap c R θ - c) - (w - c)‖ := norm_sub_norm_le _ _
    have hRr₀pos : 0 < R - r₀ := sub_pos.2 hr₀lt
    -- The `θ`-integrand and its `w`-derivative.
    set G : ℂ → ℝ → ℂ := fun w θ =>
      herglotzRieszKernel c w (circleMap c R θ) * (g (circleMap c R θ) : ℂ) with hG
    set G' : ℂ → ℝ → ℂ := fun w θ =>
      (2 * (circleMap c R θ - c) / ((circleMap c R θ - c) - (w - c)) ^ 2)
        * (g (circleMap c R θ) : ℂ) with hG'
    -- `w`-derivative of the integrand, for `w ∈ s`.
    have hderiv : ∀ θ : ℝ, ∀ w ∈ s, HasDerivAt (fun w => G w θ) (G' w θ) w := by
      intro θ w hw
      have hne : (circleMap c R θ - c) - (w - c) ≠ 0 := hden (hssub hw) θ
      have hnum : HasDerivAt
          (fun w : ℂ => (circleMap c R θ - c) + (w - c)) (1 : ℂ) w := by
        simpa using ((hasDerivAt_id w).sub_const c).const_add (circleMap c R θ - c)
      have hden' : HasDerivAt
          (fun w : ℂ => (circleMap c R θ - c) - (w - c)) (-1 : ℂ) w := by
        simpa using ((hasDerivAt_id w).sub_const c).const_sub (circleMap c R θ - c)
      have hquot : HasDerivAt
          (fun w : ℂ => ((circleMap c R θ - c) + (w - c))
              / ((circleMap c R θ - c) - (w - c)))
          ((1 * ((circleMap c R θ - c) - (w - c))
              - ((circleMap c R θ - c) + (w - c)) * (-1))
            / ((circleMap c R θ - c) - (w - c)) ^ 2) w := hnum.div hden' hne
      have hgoal : HasDerivAt (fun w => G w θ)
          ((1 * ((circleMap c R θ - c) - (w - c))
              - ((circleMap c R θ - c) + (w - c)) * (-1))
            / ((circleMap c R θ - c) - (w - c)) ^ 2 * (g (circleMap c R θ) : ℂ)) w := by
        rw [hG]; simp only [herglotzRieszKernel_def]
        exact hquot.mul_const _
      convert hgoal using 2
      show 2 * (circleMap c R θ - c) / ((circleMap c R θ - c) - (w - c)) ^ 2
        = (1 * ((circleMap c R θ - c) - (w - c))
            - ((circleMap c R θ - c) + (w - c)) * (-1)) / ((circleMap c R θ - c) - (w - c)) ^ 2
      ring
    -- Uniform bound on the derivative norm by an integrable constant.
    set bound : ℝ := 2 * R / (R - r₀) ^ 2 * M with hbound
    have hG'bound : ∀ θ : ℝ, ∀ w ∈ s, ‖G' w θ‖ ≤ bound := by
      intro θ w hw
      have hz : ‖circleMap c R θ - c‖ = R := by
        rw [circleMap_sub_center]; simp [norm_circleMap_zero, abs_of_pos hR]
      have hgz : ‖(g (circleMap c R θ) : ℂ)‖ ≤ M :=
        hM _ (by rw [Metric.mem_sphere, dist_eq_norm]; exact hz)
      have hlb : R - r₀ ≤ ‖(circleMap c R θ - c) - (w - c)‖ := hdenlb w hw θ
      have h1 : ‖2 * (circleMap c R θ - c)‖ = 2 * R := by
        rw [norm_mul, hz]; norm_num
      have h2 : (R - r₀) ^ 2 ≤ ‖(circleMap c R θ - c) - (w - c)‖ ^ 2 :=
        pow_le_pow_left₀ hRr₀pos.le hlb 2
      have hgz0 : 0 ≤ ‖(g (circleMap c R θ) : ℂ)‖ := norm_nonneg _
      rw [hG', norm_mul, norm_div, norm_pow, h1, hbound]
      have hdiv : 2 * R / ‖(circleMap c R θ - c) - (w - c)‖ ^ 2 ≤ 2 * R / (R - r₀) ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity) h2
      have hdivnn : 0 ≤ 2 * R / ‖(circleMap c R θ - c) - (w - c)‖ ^ 2 := by positivity
      exact mul_le_mul hdiv hgz hgz0 (le_trans hdivnn hdiv)
    -- Differentiation under the integral sign for the underlying interval integral.
    have hcontG : ∀ w ∈ Metric.ball c R, Continuous (fun θ : ℝ => G w θ) := by
      intro w hw
      have := (hcont hw).comp_continuous (continuous_circleMap c R)
        (fun θ => circleMap_mem_sphere c hR.le θ)
      simpa [hG, Function.comp_def] using this
    have hgc : Continuous (fun θ : ℝ => (g (circleMap c R θ) : ℂ)) := by
      apply Complex.continuous_ofReal.comp
      exact hg.comp_continuous (continuous_circleMap c R)
        (fun θ => circleMap_mem_sphere c hR.le θ)
    have hFmeas : ∀ᶠ w in 𝓝 w₀, AEStronglyMeasurable (G w)
        (volume.restrict (Set.uIoc 0 (2 * π))) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (hssub (Metric.mem_ball_self hρpos))] with w hw
      exact (hcontG w hw).aestronglyMeasurable.restrict
    have hFint : IntervalIntegrable (G w₀) volume 0 (2 * π) :=
      (hcontG w₀ hw₀).intervalIntegrable 0 (2 * π)
    have hF'meas : AEStronglyMeasurable (G' w₀) (volume.restrict (Set.uIoc 0 (2 * π))) := by
      have hcG' : Continuous (fun θ : ℝ => G' w₀ θ) := by
        have hne : ∀ θ : ℝ, ((circleMap c R θ - c) - (w₀ - c)) ^ 2 ≠ 0 := by
          intro θ; exact pow_ne_zero _ (hden hw₀ θ)
        rw [hG']
        apply Continuous.mul _ (by fun_prop)
        apply Continuous.div (by fun_prop) (by fun_prop) hne
      exact hcG'.aestronglyMeasurable.restrict
    have hkey := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := G) (F' := G') (x₀ := w₀) (bound := fun _ => bound) (s := s)
      hsnhds hFmeas hFint hF'meas
      (by
        apply ae_of_all
        intro θ _ w hw
        exact hG'bound θ w hw)
      (intervalIntegrable_const)
      (by
        apply ae_of_all
        intro θ _ w hw
        exact hderiv θ w hw)
    -- Assemble: `F = (2π)⁻¹ * (interval integral)`, hence differentiable at `w₀`.
    have hFeq : F = fun w => ((2 * π : ℝ)⁻¹ : ℂ) * (∫ θ in (0)..(2 * π), G w θ) := by
      rw [hF]; ext w
      rw [Real.circleAverage_def]
      change ((2 * π : ℝ)⁻¹ : ℝ) • (∫ θ in (0)..(2 * π), G w θ) = _
      rw [Complex.real_smul]
      norm_num
    rw [hFeq]
    have hHD : HasDerivAt (fun w => ((2 * π : ℝ)⁻¹ : ℂ) * (∫ θ in (0)..(2 * π), G w θ))
        (((2 * π : ℝ)⁻¹ : ℂ) * (∫ θ in (0)..(2 * π), G' w₀ θ)) w₀ :=
      hkey.2.const_mul ((2 * π : ℝ)⁻¹ : ℂ)
    exact hHD.differentiableAt.differentiableWithinAt
  -- Conclude harmonicity pointwise on the open ball.
  intro w₀ hw₀
  have hanalytic : AnalyticAt ℂ F w₀ :=
    (hFdiff.analyticOnNhd Metric.isOpen_ball) w₀ hw₀
  have hharm : InnerProductSpace.HarmonicAt (fun w => (F w).re) w₀ :=
    AnalyticAt.harmonicAt_re hanalytic
  rw [InnerProductSpace.harmonicAt_congr_nhds
    (Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hw₀) hreF)] at hharm
  exact hharm

/-- **Boundary values of the Poisson integral (the Dirichlet problem on a disk).** For boundary data
`g` continuous on the circle `{|z - c| = R}`, the Poisson integral converges to `g ζ` at every
boundary point `ζ` as the interior point approaches `ζ` from inside the disk. Together with
`poissonIntegral_harmonicOn`, this solves the Dirichlet problem on the disk for continuous boundary
data. (Continuity on the whole circle — not merely at `ζ` — is needed: it supplies the
integrability and the uniform bound of `g` that the Poisson kernel's approximate-identity argument
consumes over the entire circle.) -/
theorem poissonIntegral_tendsto_boundary (g : ℂ → ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hg : ContinuousOn g (Metric.sphere c R)) {ζ : ℂ} (hζ : ζ ∈ Metric.sphere c R) :
    Tendsto (poissonIntegral g c R) (𝓝[Metric.ball c R] ζ) (𝓝 (g ζ)) := by
  classical
  -- `‖ζ - c‖ = R`, since `ζ` lies on the boundary circle.
  have hζc : ‖ζ - c‖ = R := by simpa [dist_eq_norm] using hζ
  -- `g` is bounded by `M ≥ 0` on the (compact) boundary circle.
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z ∈ Metric.sphere c R, |g z| ≤ M :=
    (isCompact_sphere c R).exists_bound_of_continuousOn (f := fun z => g z) hg
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM ζ hζ)
  -- Membership facts and the sphere norm.
  have hsphere : ∀ θ : ℝ, ‖circleMap c R θ - c‖ = R := by
    intro θ; rw [circleMap_sub_center]; simp [norm_circleMap_zero, abs_of_pos hR]
  -- For `w ∈ ball c R`, the kernel integrand is `CircleIntegrable`.
  have hker_ci : ∀ {w : ℂ}, w ∈ Metric.ball c R →
      CircleIntegrable (fun z => poissonKernel c w z) c R := by
    intro w hw
    have hcont : ContinuousOn (fun z => poissonKernel c w z) (Metric.sphere c R) := by
      rw [show (fun z => poissonKernel c w z)
            = fun z => (‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖(z - c) - (w - c)‖ ^ 2 from
          funext fun z => poissonKernel_def c w z]
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro z hz
      have hzc : ‖z - c‖ = R := by simpa [dist_eq_norm] using hz
      have hwlt : ‖w - c‖ < R := by simpa [dist_eq_norm] using hw
      intro hcontra
      have hz0 : (z - c) - (w - c) = 0 := by
        have : ‖(z - c) - (w - c)‖ = 0 := by
          nlinarith [norm_nonneg ((z - c) - (w - c)), hcontra]
        simpa using this
      have : z - c = w - c := by linear_combination (norm := ring_nf) hz0
      rw [this] at hzc; exact (lt_irrefl R) (hzc ▸ hwlt)
    exact hcont.circleIntegrable hR.le
  -- For `w ∈ ball c R`, the weighted integrand is `CircleIntegrable`.
  have hwgt_ci : ∀ {w : ℂ}, w ∈ Metric.ball c R →
      CircleIntegrable (fun z => poissonKernel c w z * g z) c R := by
    intro w hw
    have hcont : ContinuousOn (fun z => poissonKernel c w z) (Metric.sphere c R) := by
      rw [show (fun z => poissonKernel c w z)
            = fun z => (‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖(z - c) - (w - c)‖ ^ 2 from
          funext fun z => poissonKernel_def c w z]
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro z hz
      have hzc : ‖z - c‖ = R := by simpa [dist_eq_norm] using hz
      have hwlt : ‖w - c‖ < R := by simpa [dist_eq_norm] using hw
      intro hcontra
      have hz0 : (z - c) - (w - c) = 0 := by
        have : ‖(z - c) - (w - c)‖ = 0 := by
          nlinarith [norm_nonneg ((z - c) - (w - c)), hcontra]
        simpa using this
      have : z - c = w - c := by linear_combination (norm := ring_nf) hz0
      rw [this] at hzc; exact (lt_irrefl R) (hzc ▸ hwlt)
    exact (hcont.mul hg).circleIntegrable hR.le
  -- P1: the kernel has total mass `1` on `ball c R`.
  have hmass : ∀ {w : ℂ}, w ∈ Metric.ball c R →
      Real.circleAverage (fun z => poissonKernel c w z) c R = 1 := by
    intro w hw
    have h := InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul
      (f := fun _ : ℂ => (1 : ℝ)) (c := c) (w := w) (R := R)
      (InnerProductSpace.harmonicOnNhd_const 1) hw
    rw [show (poissonKernel c w • fun _ : ℂ => (1 : ℝ))
          = (fun z => poissonKernel c w z) from funext fun z => by simp] at h
    exact h
  -- P2: the kernel is nonnegative on the boundary circle, for `w ∈ ball c R`.
  have hker_nonneg : ∀ {w : ℂ}, w ∈ Metric.ball c R → ∀ z ∈ Metric.sphere c R,
      0 ≤ poissonKernel c w z := by
    intro w hw z hz
    have hzc : ‖z - c‖ = R := by simpa [dist_eq_norm] using hz
    have hwlt : ‖w - c‖ < R := by simpa [dist_eq_norm] using hw
    rw [poissonKernel_def]
    apply div_nonneg _ (by positivity)
    have : ‖w - c‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hwlt.le 2
    rw [hzc]; linarith
  -- Continuity of `g` at `ζ` within the circle (ε–δ form).
  have hgζ : ContinuousWithinAt g (Metric.sphere c R) ζ := hg ζ hζ
  rw [Metric.continuousWithinAt_iff] at hgζ
  -- Main ε–δ argument.
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε₀ hε₀
  -- Choose `δ > 0` so that `|g z - g ζ| < ε₀/2` on the near arc.
  obtain ⟨δ, hδpos, hδ⟩ := hgζ (ε₀ / 2) (by linarith)
  -- Choose the final radius `δ₀`.
  refine ⟨min (δ / 2) (ε₀ * δ ^ 2 / (2 * (16 * M * R + 1))), ?_, ?_⟩
  · have h1 : 0 < δ / 2 := by linarith
    have h2 : 0 < ε₀ * δ ^ 2 / (2 * (16 * M * R + 1)) := by positivity
    exact lt_min h1 h2
  intro w hw hwζ
  -- `w` is inside the ball; record `‖w - c‖ < R` and the distance `‖w - ζ‖`.
  have hwlt : ‖w - c‖ < R := by simpa [dist_eq_norm] using hw
  have hwζnorm : ‖w - ζ‖ < min (δ / 2) (ε₀ * δ ^ 2 / (2 * (16 * M * R + 1))) := by
    simpa [dist_eq_norm] using hwζ
  have hwζ2 : ‖w - ζ‖ < δ / 2 := lt_of_lt_of_le hwζnorm (min_le_left _ _)
  have hwζ3 : ‖w - ζ‖ < ε₀ * δ ^ 2 / (2 * (16 * M * R + 1)) :=
    lt_of_lt_of_le hwζnorm (min_le_right _ _)
  have hwζ0 : 0 ≤ ‖w - ζ‖ := norm_nonneg _
  -- The numerator `K = R² - ‖w-c‖² ≥ 0`, and `K ≤ 2R‖w-ζ‖`.
  set K : ℝ := R ^ 2 - ‖w - c‖ ^ 2 with hK
  have hKnonneg : 0 ≤ K := by
    have : ‖w - c‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hwlt.le 2
    rw [hK]; linarith
  have hKle : K ≤ 2 * R * ‖w - ζ‖ := by
    have hrw : R - ‖w - c‖ ≤ ‖w - ζ‖ := by
      have := norm_sub_norm_le (ζ - c) (w - c)
      rw [hζc] at this
      have he : (ζ - c) - (w - c) = -(w - ζ) := by ring
      rw [he, norm_neg] at this
      linarith
    have hRle : R + ‖w - c‖ ≤ 2 * R := by linarith
    have hfac : K = (R - ‖w - c‖) * (R + ‖w - c‖) := by rw [hK]; ring
    rw [hfac]
    calc (R - ‖w - c‖) * (R + ‖w - c‖)
        ≤ ‖w - ζ‖ * (R + ‖w - c‖) := by
          apply mul_le_mul_of_nonneg_right hrw (by linarith [norm_nonneg (w - c)])
      _ ≤ ‖w - ζ‖ * (2 * R) := by
          apply mul_le_mul_of_nonneg_left hRle hwζ0
      _ = 2 * R * ‖w - ζ‖ := by ring
  -- The far-arc denominator lower bound and its consequence.
  have hδmζ : 0 < δ - ‖w - ζ‖ := by linarith
  -- The constant far bound `B := 2 M K / (δ - ‖w-ζ‖)²`.
  set B : ℝ := 2 * M * K / (δ - ‖w - ζ‖) ^ 2 with hB
  have hBnonneg : 0 ≤ B := by rw [hB]; positivity
  -- Pointwise bound on the whole circle:
  -- `kernel z * |g z - g ζ| ≤ ε₀/2 * kernel z + B`.
  have hptwise : ∀ z ∈ Metric.sphere c R,
      poissonKernel c w z * |g z - g ζ| ≤ ε₀ / 2 * poissonKernel c w z + B := by
    intro z hz
    have hzc : ‖z - c‖ = R := by simpa [dist_eq_norm] using hz
    have hk0 : 0 ≤ poissonKernel c w z := hker_nonneg hw z hz
    by_cases hnear : ‖z - ζ‖ < δ
    · -- Near arc: `|g z - g ζ| < ε₀/2`.
      have hgz : |g z - g ζ| < ε₀ / 2 := by
        have := hδ (x := z) hz (by simpa [dist_eq_norm] using hnear)
        simpa [Real.dist_eq] using this
      calc poissonKernel c w z * |g z - g ζ|
          ≤ poissonKernel c w z * (ε₀ / 2) :=
            mul_le_mul_of_nonneg_left hgz.le hk0
        _ = ε₀ / 2 * poissonKernel c w z := by ring
        _ ≤ ε₀ / 2 * poissonKernel c w z + B := by linarith
    · -- Far arc: `|g z - g ζ| ≤ 2M` and `kernel z ≤ K / (δ - ‖w-ζ‖)²`.
      rw [not_lt] at hnear
      have hgz : |g z - g ζ| ≤ 2 * M := by
        have h1 : |g z| ≤ M := hM z hz
        have h2 : |g ζ| ≤ M := hM ζ hζ
        calc |g z - g ζ| ≤ |g z| + |g ζ| := abs_sub _ _
          _ ≤ 2 * M := by linarith
      -- denominator lower bound `δ - ‖w-ζ‖ ≤ ‖(z-c)-(w-c)‖`.
      have hdenlb : δ - ‖w - ζ‖ ≤ ‖(z - c) - (w - c)‖ := by
        have htri : ‖z - ζ‖ - ‖w - ζ‖ ≤ ‖z - w‖ := by
          have h := norm_sub_norm_le (z - ζ) (w - ζ)
          have he : (z - ζ) - (w - ζ) = z - w := by ring
          rw [he] at h; exact h
        have heq : (z - c) - (w - c) = z - w := by ring
        rw [heq]; linarith
      -- Hence the kernel is at most `K / (δ - ‖w-ζ‖)²` on the far arc.
      have hkfar : poissonKernel c w z ≤ K / (δ - ‖w - ζ‖) ^ 2 := by
        rw [poissonKernel_def, hzc, ← hK]
        apply div_le_div_of_nonneg_left hKnonneg (by positivity)
        exact pow_le_pow_left₀ hδmζ.le hdenlb 2
      -- Combine: `kernel z * |g z - g ζ| ≤ kernel z * 2M ≤ B`.
      calc poissonKernel c w z * |g z - g ζ|
          ≤ poissonKernel c w z * (2 * M) :=
            mul_le_mul_of_nonneg_left hgz hk0
        _ ≤ K / (δ - ‖w - ζ‖) ^ 2 * (2 * M) :=
            mul_le_mul_of_nonneg_right hkfar (by linarith)
        _ = B := by rw [hB]; ring
        _ ≤ ε₀ / 2 * poissonKernel c w z + B := by
            have : 0 ≤ ε₀ / 2 * poissonKernel c w z := by positivity
            linarith
  -- Average the pointwise bound.
  have hRabs : |R| = R := abs_of_pos hR
  -- The dominating function is `CircleIntegrable` (continuous on the circle).
  have hdom_ci : CircleIntegrable
      (fun z => ε₀ / 2 * poissonKernel c w z + B) c R := by
    have h1 : CircleIntegrable (fun z => ε₀ / 2 * poissonKernel c w z) c R := by
      have h := hker_ci hw
      rw [circleIntegrable_def] at h ⊢
      exact h.const_mul _
    exact h1.add (circleIntegrable_const B c R)
  -- The integrand `kernel * |g - gζ|` is `CircleIntegrable`.
  have hint_ci : CircleIntegrable
      (fun z => poissonKernel c w z * |g z - g ζ|) c R := by
    have hcont : ContinuousOn (fun z => poissonKernel c w z) (Metric.sphere c R) := by
      rw [show (fun z => poissonKernel c w z)
            = fun z => (‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖(z - c) - (w - c)‖ ^ 2 from
          funext fun z => poissonKernel_def c w z]
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro z hz
      have hzc : ‖z - c‖ = R := by simpa [dist_eq_norm] using hz
      intro hcontra
      have hz0 : (z - c) - (w - c) = 0 := by
        have : ‖(z - c) - (w - c)‖ = 0 := by
          nlinarith [norm_nonneg ((z - c) - (w - c)), hcontra]
        simpa using this
      have : z - c = w - c := by linear_combination (norm := ring_nf) hz0
      rw [this] at hzc; exact (lt_irrefl R) (hzc ▸ hwlt)
    have hcont2 : ContinuousOn (fun z => |g z - g ζ|) (Metric.sphere c R) := by
      apply ContinuousOn.abs
      exact hg.sub continuousOn_const
    exact (hcont.mul hcont2).circleIntegrable hR.le
  -- The chain of inequalities for `|P w - g ζ|`.
  have hkey : |poissonIntegral g c R w - g ζ| ≤ ε₀ / 2 + B := by
    -- Rewrite `P w - g ζ` as an average of `kernel * (g - g ζ)`.
    have hrewrite : poissonIntegral g c R w - g ζ
        = Real.circleAverage (fun z => poissonKernel c w z * (g z - g ζ)) c R := by
      have hsub : (fun z => poissonKernel c w z * (g z - g ζ))
          = fun z => poissonKernel c w z * g z - g ζ * poissonKernel c w z := by
        funext z; ring
      rw [poissonIntegral, hsub,
        Real.circleAverage_fun_sub (hwgt_ci hw) ((hker_ci hw).smul (g ζ) |>.congr ?_)]
      · rw [show (fun z => g ζ * poissonKernel c w z)
              = fun z => g ζ • poissonKernel c w z from funext fun z => by simp [smul_eq_mul]]
        rw [Real.circleAverage_fun_smul, hmass hw, smul_eq_mul, mul_one]
      · intro θ; simp [smul_eq_mul]
    rw [hrewrite]
    -- `|avg| ≤ avg |·| = avg (kernel * |g - gζ|) ≤ ε₀/2 + B`.
    calc |Real.circleAverage (fun z => poissonKernel c w z * (g z - g ζ)) c R|
        ≤ Real.circleAverage |fun z => poissonKernel c w z * (g z - g ζ)| c R :=
          Real.abs_circleAverage_le_circleAverage_abs
      _ = Real.circleAverage (fun z => poissonKernel c w z * |g z - g ζ|) c R := by
          apply Real.circleAverage_congr_sphere
          intro z hz
          rw [hRabs] at hz
          change |poissonKernel c w z * (g z - g ζ)| = poissonKernel c w z * |g z - g ζ|
          rw [abs_mul, abs_of_nonneg (hker_nonneg hw z hz)]
      _ ≤ Real.circleAverage (fun z => ε₀ / 2 * poissonKernel c w z + B) c R := by
          apply Real.circleAverage_mono hint_ci hdom_ci
          intro z hz; rw [hRabs] at hz; exact hptwise z hz
      _ = ε₀ / 2 + B := by
          rw [show (fun z => ε₀ / 2 * poissonKernel c w z + B)
                = (fun z => ε₀ / 2 * poissonKernel c w z) + (fun _ => B) from
              funext fun z => rfl]
          rw [Real.circleAverage_add ((hker_ci hw).smul (ε₀ / 2) |>.congr ?_)
              (circleIntegrable_const B c R)]
          · rw [show (fun z => ε₀ / 2 * poissonKernel c w z)
                  = fun z => (ε₀ / 2) • poissonKernel c w z from
                funext fun z => by simp [smul_eq_mul]]
            rw [Real.circleAverage_fun_smul, hmass hw, Real.circleAverage_const, smul_eq_mul,
              mul_one]
          · intro θ; simp [smul_eq_mul]
  -- Finally, bound `B < ε₀/2`.
  have hBsmall : B < ε₀ / 2 := by
    -- `B ≤ 8 M K / δ²` and `K ≤ 2 R ‖w-ζ‖`, so `B ≤ 16 M R ‖w-ζ‖ / δ²`.
    have hden_lb : (δ / 2) ^ 2 ≤ (δ - ‖w - ζ‖) ^ 2 := by
      apply pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hBle1 : B ≤ 2 * M * K / (δ / 2) ^ 2 := by
      rw [hB]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) hden_lb
    have hBle2 : 2 * M * K / (δ / 2) ^ 2 ≤ 2 * M * (2 * R * ‖w - ζ‖) / (δ / 2) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left hKle (by positivity)
    have hδ2 : (δ / 2) ^ 2 = δ ^ 2 / 4 := by ring
    have hBle3 : B ≤ 16 * M * R * ‖w - ζ‖ / δ ^ 2 := by
      calc B ≤ 2 * M * (2 * R * ‖w - ζ‖) / (δ / 2) ^ 2 := le_trans hBle1 hBle2
        _ = 16 * M * R * ‖w - ζ‖ / δ ^ 2 := by rw [hδ2]; ring
    -- Now use `‖w - ζ‖ < ε₀ δ² / (2 (16 M R + 1))`.
    have hδ2pos : 0 < δ ^ 2 := by positivity
    have hfac : 0 < 16 * M * R + 1 := by positivity
    have hbound : 16 * M * R * ‖w - ζ‖ / δ ^ 2 < ε₀ / 2 := by
      rw [div_lt_iff₀ hδ2pos]
      have hkey2 : 16 * M * R * ‖w - ζ‖ ≤ (16 * M * R + 1) * ‖w - ζ‖ := by
        apply mul_le_mul_of_nonneg_right (by linarith) hwζ0
      have hlt : (16 * M * R + 1) * ‖w - ζ‖
          < (16 * M * R + 1) * (ε₀ * δ ^ 2 / (2 * (16 * M * R + 1))) := by
        apply mul_lt_mul_of_pos_left hwζ3 hfac
      have heq : (16 * M * R + 1) * (ε₀ * δ ^ 2 / (2 * (16 * M * R + 1)))
          = ε₀ / 2 * δ ^ 2 := by field_simp
      calc 16 * M * R * ‖w - ζ‖ ≤ (16 * M * R + 1) * ‖w - ζ‖ := hkey2
        _ < (16 * M * R + 1) * (ε₀ * δ ^ 2 / (2 * (16 * M * R + 1))) := hlt
        _ = ε₀ / 2 * δ ^ 2 := heq
    linarith [hBle3]
  -- Conclude.
  rw [Real.dist_eq]
  linarith [hkey]

end RiemannDynamics
