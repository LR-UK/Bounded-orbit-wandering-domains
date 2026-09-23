/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Potential.PoissonDirichlet
import Mathlib.Analysis.Complex.Harmonic.MeanValue

/-!
# Harnack's principle and the strong minimum principle for harmonic functions

Two convergence/rigidity facts about harmonic functions that Mathlib does not provide, needed to
prove harmonicity of the Perron envelope:

* **Strong minimum principle** (`harmonic_eq_zero_of_nonneg_eq_zero`): a nonnegative harmonic
  function on a connected open set that vanishes at one interior point vanishes identically. (The
  mean-value equality forces a nonnegative harmonic function attaining its minimum `0` at an
  interior point to be `0` on a whole circle, hence on a ball; the zero set is then clopen.)
* **Harnack's principle** (`harmonicOnNhd_of_monotone_tendsto`): the pointwise limit of a monotone
  increasing, locally bounded-above sequence of harmonic functions is harmonic. (Harnack's
  inequality — itself read off the Poisson-kernel bounds — upgrades the monotone pointwise
  convergence to local uniform convergence; the locally uniform limit is continuous, and equals the
  Poisson integral of its continuous boundary values, hence harmonic by
  `poissonIntegral_harmonicOn`.)

## Main statements

* `harmonic_eq_zero_of_nonneg_eq_zero` — the strong minimum principle;
* `harmonicOnNhd_of_monotone_tendsto` — Harnack's principle (monotone harmonic limits).
-/

open MeasureTheory Filter Metric Topology
open scoped Real Topology

namespace RiemannDynamics

/-- **Strong minimum principle for harmonic functions.** A harmonic function on a preconnected open
set `U` that is nonnegative throughout and vanishes at one point of `U` is identically zero on `U`.
(At a zero `z₀`, the mean-value equality `0 = f z₀ = ⨍_{|z-z₀|=r} f` of a nonnegative `f` forces
`f = 0` on each small circle, hence on a ball; the zero set is thus open, and closed by continuity,
so it is all of the connected `U`.) -/
theorem harmonic_eq_zero_of_nonneg_eq_zero {U : Set ℂ} (hUopen : IsOpen U)
    (hUconn : IsPreconnected U) {f : ℂ → ℝ} (hf : InnerProductSpace.HarmonicOnNhd f U)
    (hnonneg : ∀ z ∈ U, 0 ≤ f z) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hf0 : f z₀ = 0) :
    ∀ z ∈ U, f z = 0 := by
  classical
  set A : Set ℂ := U ∩ f ⁻¹' {0} with hA
  -- It suffices to show `U ⊆ A`.
  suffices hAU : U ⊆ A by intro z hz; exact (hAU hz).2
  -- `A` is open in `ℂ`: at each zero `z`, `f` vanishes on a whole ball.
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨hzU, hzf⟩ := hz
    have hfz : f z = 0 := hzf
    -- A closed ball `closedBall z r₀ ⊆ U`.
    obtain ⟨r₀, hr₀pos, hr₀sub⟩ : ∃ r₀ > 0, Metric.closedBall z r₀ ⊆ U := by
      obtain ⟨r₀, hr₀pos, hr₀sub⟩ := Metric.nhds_basis_closedBall.mem_iff.1
        (hUopen.mem_nhds hzU)
      exact ⟨r₀, hr₀pos, hr₀sub⟩
    -- On every circle `sphere z r` with `0 < r ≤ r₀`, `f` vanishes.
    have hcircle : ∀ r, 0 < r → r ≤ r₀ → ∀ x ∈ Metric.sphere z r, f x = 0 := by
      intro r hrpos hrle x hx
      -- `f` is harmonic on `closedBall z |r| ⊆ closedBall z r₀ ⊆ U`.
      have hsub : Metric.closedBall z |r| ⊆ U := by
        rw [abs_of_pos hrpos]
        exact (Metric.closedBall_subset_closedBall hrle).trans hr₀sub
      have hharm : InnerProductSpace.HarmonicOnNhd f (Metric.closedBall z |r|) := hf.mono hsub
      -- The circle `sphere z r` lies inside `U`.
      have hsphsub : Metric.sphere z r ⊆ U := fun w hw =>
        hr₀sub (Metric.closedBall_subset_closedBall hrle
          (Metric.sphere_subset_closedBall hw))
      -- Mean value: `circleAverage f z r = f z = 0`.
      have hmv : Real.circleAverage f z r = 0 := by
        rw [InnerProductSpace.HarmonicOnNhd.circleAverage_eq hharm, hfz]
      -- The angular integrand `g θ := f (circleMap z r θ)`.
      set g : ℝ → ℝ := fun θ => f (circleMap z r θ) with hg
      -- Each `circleMap z r θ` lies on `sphere z r ⊆ U`.
      have hmem : ∀ θ, circleMap z r θ ∈ Metric.sphere z r := fun θ => by
        have := circleMap_mem_sphere' z r θ; rwa [abs_of_pos hrpos] at this
      -- `g` is continuous.
      have hgcont : Continuous g :=
        (hf.continuousOn.mono hsphsub).comp_continuous (by fun_prop) (fun θ => hmem θ)
      -- `g` is nonnegative on `[0, 2π]` (points lie on `sphere z r ⊆ U`).
      have hgnn : ∀ θ, 0 ≤ g θ := fun θ => hnonneg _ (hsphsub (hmem θ))
      -- The interval integral of `g` over `[0, 2π]` is `0`.
      have hint : ∫ θ in (0)..(2 * π), g θ = 0 := by
        have := hmv
        rw [Real.circleAverage_def, smul_eq_mul] at this
        have h2 : (2 * π)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
        exact (mul_eq_zero.1 this).resolve_left h2
      -- A nonnegative continuous integrand with zero integral vanishes a.e., hence everywhere.
      have hae : g =ᵐ[volume.restrict (Set.Ioc 0 (2 * π))] 0 :=
        (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae
          (by positivity) (.of_forall (fun θ => hgnn θ))
          (hgcont.intervalIntegrable _ _)).1 hint
      have heqon : Set.EqOn g 0 (Set.Ioc 0 (2 * π)) := by
        apply MeasureTheory.Measure.eqOn_of_ae_eq hae hgcont.continuousOn
          continuousOn_const
        rw [interior_Ioc, closure_Ioo (by positivity)]
        exact Set.Ioc_subset_Icc_self
      -- Every sphere point is `circleMap z r θ` for some `θ ∈ (0, 2π]`.
      have hxr : x ∈ Metric.sphere z |r| := by rwa [abs_of_pos hrpos]
      rw [← image_circleMap_Ioc] at hxr
      obtain ⟨θ, hθ, hθx⟩ := hxr
      have := heqon hθ
      simp only [hg, Pi.zero_apply, hθx] at this
      exact this
    -- Hence `f = 0` on the whole ball `ball z r₀`, i.e. `ball z r₀ ⊆ A`.
    apply Filter.mem_of_superset (Metric.ball_mem_nhds z hr₀pos)
    intro y hy
    refine ⟨hr₀sub (Metric.ball_subset_closedBall hy), ?_⟩
    by_cases hyz : y = z
    · subst hyz; exact hfz
    · have hdpos : 0 < dist y z := dist_pos.2 hyz
      have hdle : dist y z ≤ r₀ := (Metric.mem_ball.1 hy).le
      have hymem : y ∈ Metric.sphere z (dist y z) := by
        rw [Metric.mem_sphere, dist_comm]
      exact hcircle (dist y z) hdpos hdle y hymem
  -- `A` is nonempty (contains `z₀`).
  have hAne : (U ∩ A).Nonempty := ⟨z₀, hz₀, ⟨hz₀, hf0⟩⟩
  -- Limit points of `A` inside `U` are in `A` (continuity of `f`).
  have hclosure : closure A ∩ U ⊆ A := by
    intro x hx
    obtain ⟨hxcl, hxU⟩ := hx
    refine ⟨hxU, ?_⟩
    -- `f x = 0` by continuity, as `x` is a limit of points in `A` where `f = 0`.
    have hAU : A ⊆ U := Set.inter_subset_left
    have hcwa : ContinuousWithinAt f A x :=
      (hf.continuousOn x hxU).mono hAU
    have hmaps : Set.MapsTo f A {0} := fun y hy => hy.2
    have : f x ∈ closure ({0} : Set ℝ) := hcwa.mem_closure hxcl hmaps
    simpa using this
  exact hUconn.subset_of_closure_inter_subset hAopen hAne hclosure

/-- **Harnack's principle (monotone form).** Let `Vₙ` be harmonic on the open ball `ball z₀ ρ`,
pointwise increasing in `n`, and bounded above pointwise by `Vlim`, with `Vₙ z → Vlim z` for every
`z` in the ball. Then `Vlim` is harmonic on the ball. (Harnack's inequality makes the monotone
convergence locally uniform, so `Vlim` is continuous and is the Poisson integral of its continuous
boundary values on each interior circle, hence harmonic.) -/
theorem harmonicOnNhd_of_monotone_tendsto {z₀ : ℂ} {ρ : ℝ}
    {V : ℕ → ℂ → ℝ} {Vlim : ℂ → ℝ}
    (hVharm : ∀ n, InnerProductSpace.HarmonicOnNhd (V n) (Metric.ball z₀ ρ))
    (hmono : ∀ z ∈ Metric.ball z₀ ρ, Monotone (fun n => V n z))
    (hbdd : ∀ z ∈ Metric.ball z₀ ρ, ∀ n, V n z ≤ Vlim z)
    (htends : ∀ z ∈ Metric.ball z₀ ρ, Tendsto (fun n => V n z) atTop (𝓝 (Vlim z))) :
    InnerProductSpace.HarmonicOnNhd Vlim (Metric.ball z₀ ρ) := by
  intro w hw
  -- Choose `r > 0` with `closedBall w (2r) ⊆ ball z₀ ρ`.
  obtain ⟨r, hrpos, hrsub⟩ : ∃ r > 0, Metric.closedBall w (2 * r) ⊆ Metric.ball z₀ ρ := by
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1
      (Metric.isOpen_ball.mem_nhds hw)
    exact ⟨δ / 2, by positivity, by rwa [mul_div_cancel₀ _ (two_ne_zero)]⟩
  have h2rpos : (0 : ℝ) < 2 * r := by positivity
  -- Useful subset facts.
  have hcb_r : Metric.closedBall w r ⊆ Metric.closedBall w (2 * r) :=
    Metric.closedBall_subset_closedBall (by linarith)
  have hballsub : Metric.closedBall w (2 * r) ⊆ Metric.ball z₀ ρ := hrsub
  -- Each `V n` is harmonic on `closedBall w (2r)`.
  have hVn2r : ∀ n, InnerProductSpace.HarmonicOnNhd (V n) (Metric.closedBall w (2 * r)) :=
    fun n => (hVharm n).mono hballsub
  -- `V n ≤ V (n+1)` and `V n ≤ Vlim` on `closedBall w (2r)`; monotone in `n`.
  have hmono2r : ∀ y ∈ Metric.closedBall w (2 * r), Monotone (fun n => V n y) :=
    fun y hy => hmono y (hballsub hy)
  have hbdd2r : ∀ y ∈ Metric.closedBall w (2 * r), ∀ n, V n y ≤ Vlim y :=
    fun y hy => hbdd y (hballsub hy)
  have htends2r : ∀ y ∈ Metric.closedBall w (2 * r),
      Tendsto (fun n => V n y) atTop (𝓝 (Vlim y)) := fun y hy => htends y (hballsub hy)
  -- `w` lies in the open ball `ball w (2r)`.
  have hwmem : w ∈ Metric.ball w (2 * r) := by simp [Metric.mem_ball, h2rpos]
  -- **Harnack's inequality** on `closedBall w r`.
  have harnack : ∀ m n, m ≤ n → ∀ y ∈ Metric.closedBall w r,
      V n y - V m y ≤ 3 * (V n w - V m w) := by
    intro m n hmn y hy
    -- The nonnegative harmonic difference `g := V n - V m`.
    set g : ℂ → ℝ := fun z => V n z - V m z with hg
    have hgharm : InnerProductSpace.HarmonicOnNhd g (Metric.closedBall w (2 * r)) :=
      (hVn2r n).sub (hVn2r m)
    have hgnn : ∀ z ∈ Metric.closedBall w (2 * r), 0 ≤ g z := fun z hz => by
      simp only [hg]; linarith [hmono2r z hz hmn]
    -- `y` and `w` lie in `ball w (2r)`.
    have hyle : ‖y - w‖ ≤ r := by
      rw [← dist_eq_norm]; exact Metric.mem_closedBall.1 hy
    have hyball : y ∈ Metric.ball w (2 * r) := by
      rw [Metric.mem_ball, dist_eq_norm]; linarith
    -- The Poisson kernel is bounded: `0 ≤ poissonKernel w y z ≤ 3` on `sphere w (2r)`.
    have hkerbd : ∀ z ∈ Metric.sphere w (2 * r),
        0 ≤ poissonKernel w y z ∧ poissonKernel w y z ≤ 3 := by
      intro z hz
      have hzr : z ∈ Metric.sphere w (2 * r) := hz
      have hker : poissonKernel w y z = ((z - w + (y - w)) / ((z - w) - (y - w))).re := by
        rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
          herglotzRieszKernel_def]
      constructor
      · rw [hker]
        refine le_trans ?_ (le_re_herglotzRieszKernel hzr hyball)
        apply div_nonneg <;> [skip; positivity]
        · linarith
      · rw [hker]
        refine le_trans (re_herglotzRieszKernel_le hzr hyball) ?_
        rw [div_le_iff₀ (by linarith)]
        linarith
    -- Reproducing formula for `g` at `y`, mean value at `w`.
    have hrepr : Real.circleAverage (poissonKernel w y • g) w (2 * r) = g y :=
      InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul hgharm hyball
    have hmean : Real.circleAverage g w (2 * r) = g w :=
      InnerProductSpace.HarmonicOnNhd.circleAverage_eq (R := 2 * r) (c := w) (f := g)
        (by rwa [abs_of_pos h2rpos])
    -- Circle integrability of the relevant integrands.
    have hgcont_sph : ContinuousOn g (Metric.sphere w (2 * r)) :=
      hgharm.continuousOn.mono Metric.sphere_subset_closedBall
    have hgci : CircleIntegrable g w (2 * r) := hgcont_sph.circleIntegrable h2rpos.le
    have hkercont : ContinuousOn (fun z => poissonKernel w y z * g z)
        (Metric.sphere w (2 * r)) := by
      apply ContinuousOn.mul ?_ hgcont_sph
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      apply Complex.continuous_re.comp_continuousOn
      rw [herglotzRieszKernel_fun_def]
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro z hz
      have hzn : ‖z - w‖ = 2 * r := by
        rw [← dist_eq_norm]; simpa using (Metric.mem_sphere.1 hz)
      intro hcontra
      have : z - w = y - w := by linear_combination (norm := ring_nf) hcontra
      rw [this] at hzn; rw [hzn] at hyle; linarith
    have hkci : CircleIntegrable (fun z => poissonKernel w y z * g z) w (2 * r) :=
      hkercont.circleIntegrable h2rpos.le
    have h3gci : CircleIntegrable (fun z => 3 * g z) w (2 * r) :=
      ((continuousOn_const.mul hgcont_sph)).circleIntegrable h2rpos.le
    -- The pointwise bound, then circle-average monotonicity.
    have hpt : ∀ z ∈ Metric.sphere w |2 * r|, poissonKernel w y z * g z ≤ 3 * g z := by
      intro z hz
      rw [abs_of_pos h2rpos] at hz
      obtain ⟨hk0, hk3⟩ := hkerbd z hz
      have hgz : 0 ≤ g z := hgnn z (Metric.sphere_subset_closedBall hz)
      nlinarith [hk3, hgz]
    calc g y = Real.circleAverage (poissonKernel w y • g) w (2 * r) := hrepr.symm
      _ = Real.circleAverage (fun z => poissonKernel w y z * g z) w (2 * r) := by
          apply Real.circleAverage_congr_sphere; intro z _; simp [smul_eq_mul]
      _ ≤ Real.circleAverage (fun z => 3 * g z) w (2 * r) :=
          Real.circleAverage_mono hkci h3gci hpt
      _ = 3 * Real.circleAverage g w (2 * r) := by
          rw [show (fun z => (3 : ℝ) * g z) = (fun z => (3 : ℝ) • g z) by
            simp [smul_eq_mul], Real.circleAverage_fun_smul, smul_eq_mul]
      _ = 3 * (V n w - V m w) := by rw [hmean]
  -- The "gap" `D m := Vlim w - V m w` tends to `0` and is nonnegative.
  set D : ℕ → ℝ := fun m => Vlim w - V m w with hD
  have hDtends : Tendsto D atTop (𝓝 0) := by
    have := (htends w hw).const_sub (Vlim w)
    simpa [hD] using this
  have hDnn : ∀ m, 0 ≤ D m := fun m => by
    simp only [hD]; linarith [hbdd w hw m]
  -- **Uniform estimate**: `0 ≤ Vlim y - V m y ≤ 3 * D m` on `closedBall w r`.
  have hunifest : ∀ m, ∀ y ∈ Metric.closedBall w r,
      |Vlim y - V m y| ≤ 3 * D m := by
    intro m y hy
    have hycb : y ∈ Metric.closedBall w (2 * r) := hcb_r hy
    -- `Vlim y - V m y ≥ 0`.
    have hnn : 0 ≤ Vlim y - V m y := by linarith [hbdd2r y hycb m]
    rw [abs_of_nonneg hnn]
    -- Pass the Harnack inequality to the limit `n → ∞`.
    have hlhs : Tendsto (fun n => V n y - V m y) atTop (𝓝 (Vlim y - V m y)) :=
      (htends2r y hycb).sub_const (V m y)
    have hrhs : Tendsto (fun n => 3 * (V n w - V m w)) atTop (𝓝 (3 * D m)) := by
      have : Tendsto (fun n => V n w - V m w) atTop (𝓝 (Vlim w - V m w)) :=
        (htends w hw).sub_const (V m w)
      simpa [hD] using this.const_mul 3
    refine le_of_tendsto_of_tendsto hlhs hrhs ?_
    filter_upwards [Filter.eventually_ge_atTop m] with n hn
    exact harnack m n hn y hy
  -- Hence `V` tends to `Vlim` uniformly on `closedBall w r`.
  have hunif : TendstoUniformlyOn V Vlim atTop (Metric.closedBall w r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    -- From `3 * D m < ε` eventually.
    have : Tendsto (fun m => 3 * D m) atTop (𝓝 0) := by
      simpa using hDtends.const_mul 3
    filter_upwards [this.eventually (eventually_lt_nhds hε)] with m hm
    intro y hy
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hunifest m y hy) hm
  -- `Vlim` is continuous on `closedBall w r`, in particular on `sphere w r`.
  have hVlimcont_cb : ContinuousOn Vlim (Metric.closedBall w r) :=
    hunif.continuousOn (.of_forall (fun n =>
      ((hVharm n).mono (hcb_r.trans hballsub)).continuousOn))
  have hVlimcont_sph : ContinuousOn Vlim (Metric.sphere w r) :=
    hVlimcont_cb.mono Metric.sphere_subset_closedBall
  -- On `ball w r`, `Vlim` equals its Poisson integral.
  have hVlim_poisson : ∀ y ∈ Metric.ball w r,
      Vlim y = poissonIntegral Vlim w r y := by
    intro y hy
    have hyle : ‖y - w‖ < r := by rw [← dist_eq_norm]; exact Metric.mem_ball.1 hy
    -- The Poisson kernel `z ↦ poissonKernel w y z` is continuous on `sphere w r`.
    have hkcont : ContinuousOn (fun z => poissonKernel w y z) (Metric.sphere w r) := by
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      apply Complex.continuous_re.comp_continuousOn
      rw [herglotzRieszKernel_fun_def]
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro z hz
      have hzn : ‖z - w‖ = r := by rw [← dist_eq_norm]; simpa using (Metric.mem_sphere.1 hz)
      intro hcontra
      have : z - w = y - w := by linear_combination (norm := ring_nf) hcontra
      rw [this] at hzn; rw [hzn] at hyle; linarith
    -- A fixed constant `K := ⨍ |poissonKernel w y|`.
    set K : ℝ := Real.circleAverage (fun z => |poissonKernel w y z|) w r with hK
    -- `V n` reproduces itself: `V n y = poissonIntegral (V n) w r y`.
    have hVrepr : ∀ n, V n y = poissonIntegral (V n) w r y := by
      intro n
      have hVcb : InnerProductSpace.HarmonicOnNhd (V n) (Metric.closedBall w r) :=
        (hVn2r n).mono hcb_r
      have := InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul hVcb hy
      rw [poissonIntegral]
      rw [← this]
      apply Real.circleAverage_congr_sphere; intro z _; simp [smul_eq_mul]
    -- Continuity / integrability facts for the kernel-weighted integrands.
    have hciK : CircleIntegrable (fun z => |poissonKernel w y z|) w r :=
      (hkcont.abs).circleIntegrable hrpos.le
    have hci_kf : ∀ h : ℂ → ℝ, ContinuousOn h (Metric.sphere w r) →
        CircleIntegrable (fun z => poissonKernel w y z * h z) w r := by
      intro h hh; exact (hkcont.mul hh).circleIntegrable hrpos.le
    -- `poissonIntegral (V n) → poissonIntegral Vlim` at `y`.
    have hVncont : ∀ n, ContinuousOn (V n) (Metric.sphere w r) :=
      fun n => ((hVn2r n).mono hcb_r).continuousOn.mono Metric.sphere_subset_closedBall
    have hbound : ∀ n, |poissonIntegral (V n) w r y - poissonIntegral Vlim w r y|
        ≤ K * (3 * D n) := by
      intro n
      have hsub : poissonIntegral (V n) w r y - poissonIntegral Vlim w r y
          = Real.circleAverage (fun z => poissonKernel w y z * (V n z - Vlim z)) w r := by
        rw [poissonIntegral, poissonIntegral, ← Real.circleAverage_fun_sub
          (hci_kf _ (hVncont n)) (hci_kf _ hVlimcont_sph)]
        apply Real.circleAverage_congr_sphere; intro z _; ring_nf
      rw [hsub]
      calc |Real.circleAverage (fun z => poissonKernel w y z * (V n z - Vlim z)) w r|
          ≤ Real.circleAverage (fun z => |poissonKernel w y z * (V n z - Vlim z)|) w r :=
            Real.abs_circleAverage_le_circleAverage_abs
        _ ≤ Real.circleAverage (fun z => |poissonKernel w y z| * (3 * D n)) w r := by
            apply Real.circleAverage_mono
            · exact ((hkcont.mul (hVncont n |>.sub hVlimcont_sph)).abs).circleIntegrable hrpos.le
            · exact (hkcont.abs.mul continuousOn_const).circleIntegrable hrpos.le
            · intro z hz
              rw [abs_of_pos hrpos] at hz
              rw [abs_mul]
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
              have := hunifest n z (Metric.sphere_subset_closedBall hz)
              rwa [abs_sub_comm] at this
        _ = K * (3 * D n) := by
            have hstep : Real.circleAverage (fun z => |poissonKernel w y z| * (3 * D n)) w r
                = (3 * D n) • Real.circleAverage (fun z => |poissonKernel w y z|) w r := by
              rw [← Real.circleAverage_fun_smul (a := (3 * D n))]
              apply Real.circleAverage_congr_sphere; intro z _
              simp [smul_eq_mul, mul_comm]
            rw [hstep, smul_eq_mul, hK, mul_comm]
    have hKnn : 0 ≤ K := Real.circleAverage_nonneg_of_nonneg (fun z _ => abs_nonneg _)
    have hKDtends : Tendsto (fun n => K * (3 * D n)) atTop (𝓝 0) := by
      have : Tendsto (fun n => 3 * D n) atTop (𝓝 0) := by simpa using hDtends.const_mul 3
      simpa using this.const_mul K
    have hpoissontends : Tendsto (fun n => poissonIntegral (V n) w r y) atTop
        (𝓝 (poissonIntegral Vlim w r y)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hKDtends
      · intro n; exact dist_nonneg
      · intro n; simp only [Real.dist_eq]; exact hbound n
    -- `V n y → Vlim y` and `V n y = poissonIntegral (V n) w r y`.
    have hVny : Tendsto (fun n => V n y) atTop (𝓝 (Vlim y)) :=
      htends y (hballsub (hcb_r (Metric.ball_subset_closedBall hy)))
    have : Tendsto (fun n => poissonIntegral (V n) w r y) atTop (𝓝 (Vlim y)) := by
      simpa [hVrepr] using hVny
    exact tendsto_nhds_unique this hpoissontends
  -- The Poisson integral of `Vlim` is harmonic on `ball w r`.
  have hpoisson_harm : InnerProductSpace.HarmonicOnNhd (poissonIntegral Vlim w r)
      (Metric.ball w r) := poissonIntegral_harmonicOn Vlim w hrpos hVlimcont_sph
  -- Transfer harmonicity to `Vlim` at `w` via agreement on the neighbourhood `ball w r`.
  have hwball : w ∈ Metric.ball w r := by simp [Metric.mem_ball, hrpos]
  have heq : Vlim =ᶠ[𝓝 w] poissonIntegral Vlim w r := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hwball] with y hy using hVlim_poisson y hy
  exact (InnerProductSpace.harmonicAt_congr_nhds heq).2 (hpoisson_harm w hwball)

end RiemannDynamics
