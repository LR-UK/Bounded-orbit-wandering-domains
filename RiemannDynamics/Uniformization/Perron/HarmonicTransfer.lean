/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Potential.PerronEnvelope
import RiemannDynamics.Analysis.GrotzschRing.RingPotential

/-!
# Conformal transfer of harmonicity and subharmonicity

Plane-level bricks for Perron theory on Riemann surfaces: harmonicity and
subharmonicity are invariant under holomorphic changes of variable, so the
chart-local definitions on a surface are independent of the chart. This file
proves the invariance on `ℂ` together with the classical local facts that the
surface theory consumes:

* `harmonicAt_comp_analyticAt` — a harmonic function precomposed with a
  holomorphic map is harmonic;
* `SubharmonicOn.le_of_harmonic_majorant` — the harmonic-majorant bound on any
  bounded subdomain;
* `subharmonicOn_comp_biholo` — subharmonicity transfers along a biholomorphic
  change of variable;
* `exists_harmonicOnNhd_of_bounded_punctured` — a bounded harmonic function on
  a punctured disc extends harmonically across the puncture;
* `harnack_inequality_ball` — the two-sided Harnack inequality on concentric
  balls;
* `SubharmonicOn.eventually_eq_of_le` — the strong maximum principle: a
  subharmonic function is locally constant at an interior maximum.
-/

open Metric InnerProductSpace MeasureTheory Topology Filter
open scoped Real

namespace RiemannDynamics

/-- Precomposition with a holomorphic map preserves harmonicity: if `u` is
harmonic at `g z` and `g` is analytic at `z`, then `u ∘ g` is harmonic
at `z`. -/
theorem harmonicAt_comp_analyticAt {u : ℂ → ℝ} {g : ℂ → ℂ} {z : ℂ}
    (hu : HarmonicAt u (g z)) (hg : AnalyticAt ℂ g z) :
    HarmonicAt (u ∘ g) z := by
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff_ball.mp hu.eventually
  have huOn : HarmonicOnNhd u (ball (g z) R) := fun y hy => hball y hy
  obtain ⟨F, hFanal, hFeq⟩ := huOn.exists_analyticOnNhd_ball_re_eq
  have hcomp : AnalyticAt ℂ (F ∘ g) z := (hFanal _ (mem_ball_self hR)).comp hg
  have hFg : HarmonicAt (fun w => (F (g w)).re) z := hcomp.harmonicAt_re
  refine (harmonicAt_congr_nhds ?_).mp hFg
  have hnhds : g ⁻¹' ball (g z) R ∈ 𝓝 z :=
    hg.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hR))
  filter_upwards [hnhds] with w hw using hFeq hw

/-- The harmonic-majorant bound: a subharmonic function lies below every
harmonic function that dominates it on the frontier of a bounded subdomain. -/
theorem SubharmonicOn.le_of_harmonic_majorant {u h : ℂ → ℝ} {U D : Set ℂ}
    (hu : SubharmonicOn u U) (hD : IsOpen D) (hDb : Bornology.IsBounded D)
    (hcl : closure D ⊆ U) (hh : HarmonicOnNhd h D)
    (hhc : ContinuousOn h (closure D))
    (hle : ∀ z ∈ frontier D, u z ≤ h z) : ∀ z ∈ D, u z ≤ h z := by
  have hDU : D ⊆ U := subset_trans subset_closure hcl
  -- `u` is subharmonic on the subdomain `D`.
  have huD : SubharmonicOn u D :=
    ⟨hu.1.mono hDU, fun c hc r hr hball => hu.2 c (hDU hc) r hr (hball.trans hDU)⟩
  -- The difference `u − h` is subharmonic on `D`: circle averages split and the
  -- harmonic term satisfies the mean-value equality on every closed disk in `D`.
  have hw : SubharmonicOn (fun z => u z - h z) D := by
    refine ⟨huD.1.sub hh.continuousOn, ?_⟩
    intro c hc r hr hsub
    have hsphere : Metric.sphere c r ⊆ D := Metric.sphere_subset_closedBall.trans hsub
    have huci : CircleIntegrable u c r := (huD.1.mono hsphere).circleIntegrable hr.le
    have hhci : CircleIntegrable h c r :=
      (hh.continuousOn.mono hsphere).circleIntegrable hr.le
    rw [Real.circleAverage_fun_sub huci hhci]
    have hhavg : Real.circleAverage h c r = h c := by
      apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
      rw [abs_of_pos hr]
      exact hh.mono hsub
    have huavg : u c ≤ Real.circleAverage u c r := huD.2 c hc r hr hsub
    rw [hhavg]
    linarith
  -- `u − h` is continuous up to the closure and `≤ 0` on the frontier.
  have hwc : ContinuousOn (fun z => u z - h z) (closure D) := (hu.1.mono hcl).sub hhc
  have hwfront : ∀ z ∈ frontier D, u z - h z ≤ (0 : ℝ) := fun z hz =>
    sub_nonpos.mpr (hle z hz)
  -- The maximum principle propagates the frontier bound into `D`.
  intro z hz
  have hbound := hw.le_of_frontier_le hD hDb hwc hwfront z hz
  linarith

/-- Subharmonicity transfers along a biholomorphic change of variable: if `e`
is an open partial homeomorphism that is holomorphic in both directions and
`u` is subharmonic on `V ⊆ e.target`, then `u ∘ e` is subharmonic on the
`e`-preimage of `V`. -/
theorem subharmonicOn_comp_biholo {u : ℂ → ℝ} {V : Set ℂ}
    (e : OpenPartialHomeomorph ℂ ℂ)
    (_hf : DifferentiableOn ℂ e e.source)
    (hg : DifferentiableOn ℂ e.symm e.target)
    (hu : SubharmonicOn u V) (hVsub : V ⊆ e.target) :
    SubharmonicOn (u ∘ e) (e.source ∩ ↑e ⁻¹' V) := by
  classical
  -- Continuity of `u ∘ e` on `W := e.source ∩ e ⁻¹' V`.
  have hcont : ContinuousOn (u ∘ e) (e.source ∩ ↑e ⁻¹' V) :=
    hu.1.comp (e.continuousOn.mono Set.inter_subset_left) fun x hx => hx.2
  refine ⟨hcont, ?_⟩
  intro c hc r hr hball
  have hrne : r ≠ 0 := ne_of_gt hr
  -- The closed disk sits inside the source and its `e`-image sits inside `V`.
  have hcbsource : Metric.closedBall c r ⊆ e.source := fun x hx => (hball hx).1
  have himV : ↑e '' Metric.closedBall c r ⊆ V := by
    rintro x ⟨y, hy, rfl⟩
    exact (hball hy).2
  -- Continuity of the boundary data on the circle.
  have hueCb : ContinuousOn (u ∘ e) (Metric.closedBall c r) := hcont.mono hball
  have hueSphere : ContinuousOn (u ∘ e) (Metric.sphere c r) :=
    hueCb.mono Metric.sphere_subset_closedBall
  -- The Poisson modification `P` of `u ∘ e` on the disk.
  set P : ℂ → ℝ := poissonModify (u ∘ e) c r with hP
  have hPoff : ∀ z, z ∉ Metric.ball c r → P z = (u ∘ e) z := by
    intro z hz; simp only [hP, poissonModify, ite_eq_right hz]
  have hQharm : HarmonicOnNhd (poissonIntegral (u ∘ e) c r) (Metric.ball c r) :=
    poissonIntegral_harmonicOn (u ∘ e) c hr hueSphere
  -- `P` is harmonic on the open disk.
  have hPharm : HarmonicOnNhd P (Metric.ball c r) := by
    intro w hw
    have heqw : P =ᶠ[𝓝 w] poissonIntegral (u ∘ e) c r := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hw] with z hz
      simp only [hP, poissonModify, ite_eq_left hz]
    rw [harmonicAt_congr_nhds heqw]
    exact hQharm w hw
  -- `P` is continuous on the closed disk (Poisson boundary limit matches `u ∘ e` on the circle).
  have hPcb : ContinuousOn P (Metric.closedBall c r) := by
    have hQball : ContinuousOn (poissonIntegral (u ∘ e) c r) (Metric.ball c r) :=
      hQharm.continuousOn
    have hsplit : Metric.closedBall c r = Metric.ball c r ∪ Metric.sphere c r :=
      Metric.ball_union_sphere.symm
    intro ζ hζ
    rw [Metric.mem_closedBall] at hζ
    rcases lt_or_eq_of_le hζ with hlt | heq
    · have hζball : ζ ∈ Metric.ball c r := Metric.mem_ball.2 hlt
      have heqf : P =ᶠ[𝓝 ζ] poissonIntegral (u ∘ e) c r := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hζball] with z hz
        simp only [hP, poissonModify, ite_eq_left hz]
      have hca : ContinuousAt (poissonIntegral (u ∘ e) c r) ζ :=
        (hQball ζ hζball).continuousAt (Metric.isOpen_ball.mem_nhds hζball)
      exact (hca.congr heqf.symm).continuousWithinAt
    · have hζsphere : ζ ∈ Metric.sphere c r := Metric.mem_sphere.2 heq
      have hnotball : ζ ∉ Metric.ball c r := by rw [Metric.mem_ball, heq]; exact lt_irrefl _
      have hPζ : P ζ = (u ∘ e) ζ := hPoff ζ hnotball
      rw [hsplit]
      apply ContinuousWithinAt.union
      · have htend : Tendsto (poissonIntegral (u ∘ e) c r)
            (𝓝[Metric.ball c r] ζ) (𝓝 ((u ∘ e) ζ)) :=
          poissonIntegral_tendsto_boundary (u ∘ e) c hr hueSphere hζsphere
        have heqball : P =ᶠ[𝓝[Metric.ball c r] ζ] poissonIntegral (u ∘ e) c r := by
          filter_upwards [self_mem_nhdsWithin] with z hz
          simp only [hP, poissonModify, ite_eq_left hz]
        rw [ContinuousWithinAt, hPζ]
        exact htend.congr' heqball.symm
      · have hcwf : ContinuousWithinAt (u ∘ e) (Metric.sphere c r) ζ := hueSphere ζ hζsphere
        apply hcwf.congr (fun z hz => ?_) hPζ
        have : z ∉ Metric.ball c r := by
          rw [Metric.mem_ball, Metric.mem_sphere.1 hz]; exact lt_irrefl _
        simp only [hP, poissonModify, ite_eq_right this]
  -- The image domain `D := e '' ball c r`: open, bounded, with `closure D ⊆ V`.
  set D : Set ℂ := ↑e '' Metric.ball c r with hD
  have hDopen : IsOpen D :=
    e.isOpen_image_of_subset_source Metric.isOpen_ball
      (Metric.ball_subset_closedBall.trans hcbsource)
  have hK : IsCompact (↑e '' Metric.closedBall c r) :=
    (isCompact_closedBall c r).image_of_continuousOn (e.continuousOn.mono hcbsource)
  have hDsubK : D ⊆ ↑e '' Metric.closedBall c r :=
    Set.image_mono Metric.ball_subset_closedBall
  have hclD : closure D ⊆ ↑e '' Metric.closedBall c r := closure_minimal hDsubK hK.isClosed
  have hclDV : closure D ⊆ V := hclD.trans himV
  have hDbdd : Bornology.IsBounded D := hK.isBounded.subset hDsubK
  -- The transferred majorant `P ∘ e.symm` is harmonic on `D`.
  have hharm : HarmonicOnNhd (P ∘ ↑e.symm) D := by
    rintro x ⟨y, hy, rfl⟩
    have hysource : y ∈ e.source := hcbsource (Metric.ball_subset_closedBall hy)
    have htarget : e y ∈ e.target := e.map_source hysource
    have hana : AnalyticAt ℂ (↑e.symm) (e y) := hg.analyticAt (e.open_target.mem_nhds htarget)
    have hPy : HarmonicAt P (e.symm (e y)) := by
      rw [e.left_inv hysource]
      exact hPharm y hy
    exact harmonicAt_comp_analyticAt hPy hana
  -- ... and continuous on `closure D`.
  have hmapsTo : Set.MapsTo (↑e.symm) (closure D) (Metric.closedBall c r) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hclD hx
    rw [e.left_inv (hcbsource hy)]
    exact hy
  have hhc : ContinuousOn (P ∘ ↑e.symm) (closure D) :=
    hPcb.comp (e.continuousOn_symm.mono (hclDV.trans hVsub)) hmapsTo
  -- On `frontier D ⊆ e '' sphere c r` the majorant equals `u` (`P = u ∘ e` off the open disk).
  have hle : ∀ z ∈ frontier D, u z ≤ (P ∘ ↑e.symm) z := by
    intro z hz
    rw [hDopen.frontier_eq] at hz
    obtain ⟨hzcl, hznD⟩ := hz
    obtain ⟨y, hy, rfl⟩ := hclD hzcl
    have hynb : y ∉ Metric.ball c r := fun hyb => hznD ⟨y, hyb, rfl⟩
    have hcomp : (P ∘ ↑e.symm) (e y) = P y := by
      simp only [Function.comp_apply, e.left_inv (hcbsource hy)]
    rw [hcomp, hPoff y hynb]
    exact le_of_eq rfl
  -- The harmonic-majorant bound on `D`, evaluated at `e c`.
  have hmaj : ∀ z ∈ D, u z ≤ (P ∘ ↑e.symm) z :=
    hu.le_of_harmonic_majorant hDopen hDbdd hclDV hharm hhc hle
  have hecD : (e c : ℂ) ∈ D := ⟨c, Metric.mem_ball_self hr, rfl⟩
  have hueP : u (e c) ≤ P c := by
    have hmc := hmaj (e c) hecD
    rwa [Function.comp_apply, e.left_inv hc.1] at hmc
  -- The mean value of the harmonic modification at the full radius.
  have hPcl : ContinuousOn P (closure (Metric.ball c r)) := by
    rw [closure_ball c hrne]; exact hPcb
  have hPmean : Real.circleAverage P c r = P c := by
    apply InnerProductSpace.HarmonicContOnCl.circleAverage_eq
    refine ⟨?_, ?_⟩
    · rw [abs_of_pos hr]; exact hPharm
    · rw [abs_of_pos hr]; exact hPcl
  have hPavg : Real.circleAverage P c r = Real.circleAverage (u ∘ e) c r := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    rw [abs_of_pos hr] at hz
    have hznb : z ∉ Metric.ball c r := by
      rw [Metric.mem_ball, Metric.mem_sphere.1 hz]; exact lt_irrefl _
    exact hPoff z hznb
  have hgoal : u (e c) ≤ Real.circleAverage (u ∘ e) c r := by
    calc u (e c) ≤ P c := hueP
      _ = Real.circleAverage P c r := hPmean.symm
      _ = Real.circleAverage (u ∘ e) c r := hPavg
  exact hgoal

/-- **Removable singularity for harmonic functions**: a harmonic function that
is bounded on a punctured disc extends harmonically across the puncture. -/
theorem exists_harmonicOnNhd_of_bounded_punctured {u : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hu : HarmonicOnNhd u (ball c r \ {c}))
    (hb : ∃ C, ∀ z ∈ ball c r \ {c}, |u z| ≤ C) :
    ∃ v : ℂ → ℝ, HarmonicOnNhd v (ball c r) ∧
      Set.EqOn v u (ball c r \ {c}) := by
  classical
  obtain ⟨C, hC⟩ := hb
  set ρ : ℝ := r / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  have hρr : ρ < r := by rw [hρdef]; linarith
  -- The boundary circle of the half-radius disk lies in the punctured disk.
  have hsub_sphere : sphere c ρ ⊆ ball c r \ {c} := by
    intro z hz
    have hd : dist z c = ρ := mem_sphere.1 hz
    constructor
    · exact mem_ball.2 (by rw [hd]; exact hρr)
    · intro hcon
      rw [Set.mem_singleton_iff] at hcon
      rw [hcon, dist_self] at hd
      exact absurd hd.symm (ne_of_gt hρ)
  have husph : ContinuousOn u (sphere c ρ) := hu.continuousOn.mono hsub_sphere
  have hballsub : ball c ρ ⊆ ball c r := ball_subset_ball hρr.le
  -- `C` is nonnegative.
  have hC0 : 0 ≤ C := by
    obtain ⟨z₁, hz₁⟩ := (NormedSpace.sphere_nonempty (x := c) (r := ρ)).2 hρ.le
    exact le_trans (abs_nonneg _) (hC z₁ (hsub_sphere hz₁))
  -- The Dirichlet solution on the half-radius disk, glued with `u` outside.
  have hPharm : HarmonicOnNhd (poissonIntegral u c ρ) (ball c ρ) :=
    poissonIntegral_harmonicOn u c hρ husph
  set G : ℂ → ℝ := fun z => if z ∈ ball c ρ then poissonIntegral u c ρ z else u z
    with hGdef
  have hGon : ∀ z ∈ ball c ρ, G z = poissonIntegral u c ρ z := by
    intro z hz
    simp only [hGdef]
    exact ite_eq_left hz
  have hGoff : ∀ z, z ∉ ball c ρ → G z = u z := by
    intro z hz
    simp only [hGdef]
    exact ite_eq_right hz
  -- `G` is harmonic on the open half-radius disk.
  have hGharm : HarmonicOnNhd G (ball c ρ) := by
    intro w hw
    have heqw : G =ᶠ[𝓝 w] poissonIntegral u c ρ := by
      filter_upwards [isOpen_ball.mem_nhds hw] with z hz
      exact hGon z hz
    rw [harmonicAt_congr_nhds heqw]
    exact hPharm w hw
  -- `G` is continuous up to the boundary circle (Poisson boundary limit matches `u`).
  have hGcb : ContinuousOn G (closedBall c ρ) := by
    have hPball : ContinuousOn (poissonIntegral u c ρ) (ball c ρ) := hPharm.continuousOn
    intro ζ hζ
    rcases lt_or_eq_of_le (mem_closedBall.1 hζ) with hlt | heq
    · have hζball : ζ ∈ ball c ρ := mem_ball.2 hlt
      have heqf : G =ᶠ[𝓝 ζ] poissonIntegral u c ρ := by
        filter_upwards [isOpen_ball.mem_nhds hζball] with z hz
        exact hGon z hz
      have hca : ContinuousAt (poissonIntegral u c ρ) ζ :=
        (hPball ζ hζball).continuousAt (isOpen_ball.mem_nhds hζball)
      exact (hca.congr heqf.symm).continuousWithinAt
    · have hζsphere : ζ ∈ sphere c ρ := mem_sphere.2 heq
      have hnotball : ζ ∉ ball c ρ := by rw [mem_ball, heq]; exact lt_irrefl _
      have hGζ : G ζ = u ζ := hGoff ζ hnotball
      rw [show closedBall c ρ = ball c ρ ∪ sphere c ρ from ball_union_sphere.symm]
      apply ContinuousWithinAt.union
      · have htend : Tendsto (poissonIntegral u c ρ) (𝓝[ball c ρ] ζ) (𝓝 (u ζ)) :=
          poissonIntegral_tendsto_boundary u c hρ husph hζsphere
        have heqball : G =ᶠ[𝓝[ball c ρ] ζ] poissonIntegral u c ρ := by
          filter_upwards [self_mem_nhdsWithin] with z hz
          exact hGon z hz
        rw [ContinuousWithinAt, hGζ]
        exact htend.congr' heqball.symm
      · have hcwf : ContinuousWithinAt u (sphere c ρ) ζ := husph ζ hζsphere
        apply hcwf.congr (fun z hz => ?_) hGζ
        have hznb : z ∉ ball c ρ := by rw [mem_ball, mem_sphere.1 hz]; exact lt_irrefl _
        exact hGoff z hznb
  -- `|G| ≤ C` on the closed half-radius disk, by the maximum principle.
  have hGleC : ∀ z ∈ closedBall c ρ, |G z| ≤ C := by
    have hGclcont : ContinuousOn G (closure (ball c ρ)) := by
      rw [closure_ball c hρ.ne']; exact hGcb
    have hfr1 : ∀ z ∈ frontier (ball c ρ), G z ≤ C := by
      intro z hz
      rw [frontier_ball c hρ.ne'] at hz
      have hnb : z ∉ ball c ρ := by rw [mem_ball, mem_sphere.1 hz]; exact lt_irrefl _
      rw [hGoff z hnb]
      exact le_trans (le_abs_self _) (hC z (hsub_sphere hz))
    have hfr2 : ∀ z ∈ frontier (ball c ρ), (-G) z ≤ C := by
      intro z hz
      rw [frontier_ball c hρ.ne'] at hz
      have hnb : z ∉ ball c ρ := by rw [mem_ball, mem_sphere.1 hz]; exact lt_irrefl _
      have hng : (-G) z = -(G z) := rfl
      rw [hng, hGoff z hnb]
      exact le_trans (neg_le_abs _) (hC z (hsub_sphere hz))
    have hup := (HarmonicOnNhd.subharmonicOn hGharm).le_of_frontier_le isOpen_ball
      isBounded_ball hGclcont hfr1
    have hdn := (HarmonicOnNhd.subharmonicOn hGharm.neg).le_of_frontier_le isOpen_ball
      isBounded_ball hGclcont.neg hfr2
    intro z hz
    rcases lt_or_eq_of_le (mem_closedBall.1 hz) with hlt | heq
    · have hzb : z ∈ ball c ρ := mem_ball.2 hlt
      have h9 : -(G z) ≤ C := hdn z hzb
      exact abs_le.2 ⟨by linarith, hup z hzb⟩
    · have hnb : z ∉ ball c ρ := by rw [mem_ball, heq]; exact lt_irrefl _
      rw [hGoff z hnb]
      exact hC z (hsub_sphere (mem_sphere.2 heq))
  -- The logarithmic comparison kernel is harmonic away from the puncture.
  have hLg : ∀ z : ℂ, z ≠ c → HarmonicAt (fun q : ℂ => Real.log ‖q - c‖) z := by
    intro z hz
    have h1 : AnalyticAt ℂ (fun q : ℂ => q - c) z := analyticAt_id.sub analyticAt_const
    have h2 : (fun q : ℂ => q - c) z ≠ 0 := sub_ne_zero.2 hz
    exact h1.harmonicAt_log_norm h2
  -- Two-constants estimate on the annulus `δ < |z - c| < ρ`.
  have key : ∀ δ : ℝ, 0 < δ → δ < ρ → ∀ z ∈ ball c ρ \ closedBall c δ,
      |u z - G z|
        ≤ 2 * C / (Real.log ρ - Real.log δ) * (Real.log ρ - Real.log ‖z - c‖) := by
    intro δ hδ hδρ
    have hlogpos : 0 < Real.log ρ - Real.log δ := sub_pos.2 (Real.log_lt_log hδ hδρ)
    set ε : ℝ := 2 * C / (Real.log ρ - Real.log δ) with hεdef
    have hεeq : ε * (Real.log ρ - Real.log δ) = 2 * C := by
      rw [hεdef]; exact div_mul_cancel₀ _ hlogpos.ne'
    have hAopen : IsOpen (ball c ρ \ closedBall c δ) := isOpen_ball.sdiff isClosed_closedBall
    have hAbdd : Bornology.IsBounded (ball c ρ \ closedBall c δ) :=
      isBounded_ball.subset Set.sdiff_subset
    -- Closure of the annulus and nonvanishing of `‖z - c‖` there.
    have hclA : closure (ball c ρ \ closedBall c δ) ⊆ closedBall c ρ \ ball c δ := by
      intro z hz
      rw [Set.sdiff_eq] at hz
      have h2 := closure_inter_subset_inter_closure (ball c ρ) ((closedBall c δ)ᶜ) hz
      rw [closure_ball c hρ.ne', closure_compl, interior_closedBall c hδ.ne'] at h2
      exact ⟨h2.1, h2.2⟩
    have hKne : ∀ z ∈ closedBall c ρ \ ball c δ, ‖z - c‖ ≠ 0 := by
      intro z hz
      have h1 : δ ≤ dist z c := not_lt.1 (fun hlt => hz.2 (mem_ball.2 hlt))
      rw [dist_eq_norm] at h1
      exact ne_of_gt (lt_of_lt_of_le hδ h1)
    -- The frontier of the annulus lies on the two circles.
    have hfrontier : frontier (ball c ρ \ closedBall c δ) ⊆ sphere c ρ ∪ sphere c δ := by
      intro z hz
      rw [Set.sdiff_eq] at hz
      rcases frontier_inter_subset (ball c ρ) ((closedBall c δ)ᶜ) hz with h2 | h2
      · have h3 := h2.1
        rw [frontier_ball c hρ.ne'] at h3
        exact Or.inl h3
      · have h3 := h2.2
        rw [frontier_compl, frontier_closedBall c hδ.ne'] at h3
        exact Or.inr h3
    -- Annulus and outer closed annulus sit inside the punctured disk.
    have hApunct : ball c ρ \ closedBall c δ ⊆ ball c r \ {c} := by
      intro z hz
      constructor
      · exact hballsub hz.1
      · intro hcon
        rw [Set.mem_singleton_iff] at hcon
        apply hz.2
        rw [hcon]
        exact mem_closedBall_self hδ.le
    have hKpunct : closedBall c ρ \ ball c δ ⊆ ball c r \ {c} := by
      intro z hz
      constructor
      · exact mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hz.1) hρr)
      · intro hcon
        rw [Set.mem_singleton_iff] at hcon
        apply hz.2
        rw [hcon]
        exact mem_ball_self hδ
    have hKcb : closedBall c ρ \ ball c δ ⊆ closedBall c ρ := Set.sdiff_subset
    -- One-sided comparison for a harmonic `w` vanishing on the outer circle.
    have main : ∀ w : ℂ → ℝ, HarmonicOnNhd w (ball c ρ \ closedBall c δ) →
        ContinuousOn w (closedBall c ρ \ ball c δ) →
        (∀ z ∈ sphere c ρ, w z = 0) → (∀ z ∈ sphere c δ, w z ≤ 2 * C) →
        ∀ z ∈ ball c ρ \ closedBall c δ,
          w z ≤ ε * (Real.log ρ - Real.log ‖z - c‖) := by
      intro w hwharm hwcont hwρ hwδ
      have hFharm : HarmonicOnNhd
          (fun z => w z + ε * Real.log ‖z - c‖ - ε * Real.log ρ)
          (ball c ρ \ closedBall c δ) := by
        intro z hz
        have hzc : z ≠ c := by
          intro hcon
          apply hz.2
          rw [hcon]
          exact mem_closedBall_self hδ.le
        have h1 : HarmonicAt w z := hwharm z hz
        have h2 : HarmonicAt (fun q : ℂ => Real.log ‖q - c‖) z := hLg z hzc
        have h3 := (h1.add (h2.const_smul (c := ε))).sub (harmonicAt_const (ε * Real.log ρ))
        have heq : (w + ε • fun q : ℂ => Real.log ‖q - c‖) - (fun _ => ε * Real.log ρ)
            = fun z => w z + ε * Real.log ‖z - c‖ - ε * Real.log ρ := by
          funext q
          simp [smul_eq_mul]
        rw [← heq]
        exact h3
      have hlogK : ContinuousOn (fun z : ℂ => Real.log ‖z - c‖)
          (closedBall c ρ \ ball c δ) := by
        apply ContinuousOn.log
        · fun_prop
        · exact hKne
      have hFcont : ContinuousOn (fun z => w z + ε * Real.log ‖z - c‖ - ε * Real.log ρ)
          (closure (ball c ρ \ closedBall c δ)) :=
        ((hwcont.add (continuousOn_const.mul hlogK)).sub continuousOn_const).mono hclA
      have hFfront : ∀ z ∈ frontier (ball c ρ \ closedBall c δ),
          w z + ε * Real.log ‖z - c‖ - ε * Real.log ρ ≤ 0 := by
        intro z hz
        rcases hfrontier hz with hzs | hzs
        · have hzn : ‖z - c‖ = ρ := by rw [← dist_eq_norm]; exact mem_sphere.1 hzs
          rw [hzn, hwρ z hzs]
          linarith
        · have hzn : ‖z - c‖ = δ := by rw [← dist_eq_norm]; exact mem_sphere.1 hzs
          have h2C := hwδ z hzs
          have hεeq' : ε * Real.log ρ - ε * Real.log δ = 2 * C := by
            rw [← hεeq]; ring
          rw [hzn]
          linarith
      have hle : ∀ z ∈ ball c ρ \ closedBall c δ,
          w z + ε * Real.log ‖z - c‖ - ε * Real.log ρ ≤ 0 :=
        (HarmonicOnNhd.subharmonicOn hFharm).le_of_frontier_le hAopen hAbdd hFcont hFfront
      intro z hz
      have h3 := hle z hz
      have h4 := mul_sub ε (Real.log ρ) (Real.log ‖z - c‖)
      linarith
    -- Points of the inner circle: membership facts.
    have hsphδ : ∀ z ∈ sphere c δ, z ∈ ball c r \ {c} ∧ z ∈ closedBall c ρ := by
      intro z hz
      have hd : dist z c = δ := mem_sphere.1 hz
      refine ⟨⟨mem_ball.2 (by rw [hd]; linarith), ?_⟩,
        mem_closedBall.2 (by rw [hd]; linarith)⟩
      intro hcon
      rw [Set.mem_singleton_iff] at hcon
      rw [hcon, dist_self] at hd
      exact absurd hd.symm (ne_of_gt hδ)
    -- Apply the comparison to `u - G` and `G - u`.
    have hw1harm : HarmonicOnNhd (fun z => u z - G z) (ball c ρ \ closedBall c δ) := by
      intro z hz
      exact (hu z (hApunct hz)).sub (hGharm z hz.1)
    have hw1cont : ContinuousOn (fun z => u z - G z) (closedBall c ρ \ ball c δ) :=
      (hu.continuousOn.mono hKpunct).sub (hGcb.mono hKcb)
    have hw1ρ : ∀ z ∈ sphere c ρ, u z - G z = 0 := by
      intro z hz
      have hnb : z ∉ ball c ρ := by rw [mem_ball, mem_sphere.1 hz]; exact lt_irrefl _
      rw [hGoff z hnb, sub_self]
    have hw1δ : ∀ z ∈ sphere c δ, u z - G z ≤ 2 * C := by
      intro z hz
      obtain ⟨hz1, hz2⟩ := hsphδ z hz
      have h5 := hC z hz1
      have h6 := hGleC z hz2
      have h7 : u z ≤ C := (abs_le.1 h5).2
      have h8 : -C ≤ G z := (abs_le.1 h6).1
      linarith
    have hw2harm : HarmonicOnNhd (fun z => G z - u z) (ball c ρ \ closedBall c δ) := by
      intro z hz
      exact (hGharm z hz.1).sub (hu z (hApunct hz))
    have hw2cont : ContinuousOn (fun z => G z - u z) (closedBall c ρ \ ball c δ) :=
      (hGcb.mono hKcb).sub (hu.continuousOn.mono hKpunct)
    have hw2ρ : ∀ z ∈ sphere c ρ, G z - u z = 0 := by
      intro z hz
      have hnb : z ∉ ball c ρ := by rw [mem_ball, mem_sphere.1 hz]; exact lt_irrefl _
      rw [hGoff z hnb, sub_self]
    have hw2δ : ∀ z ∈ sphere c δ, G z - u z ≤ 2 * C := by
      intro z hz
      obtain ⟨hz1, hz2⟩ := hsphδ z hz
      have h5 := hC z hz1
      have h6 := hGleC z hz2
      have h7 : G z ≤ C := (abs_le.1 h6).2
      have h8 : -C ≤ u z := (abs_le.1 h5).1
      linarith
    have h1 := main (fun z => u z - G z) hw1harm hw1cont hw1ρ hw1δ
    have h2 := main (fun z => G z - u z) hw2harm hw2cont hw2ρ hw2δ
    intro z hz
    exact abs_sub_le_iff.2 ⟨h1 z hz, h2 z hz⟩
  -- `u = G` on the punctured half-radius disk: let `δ → 0` at a fixed point.
  have claimA : ∀ z₀ ∈ ball c ρ \ {c}, u z₀ = G z₀ := by
    intro z₀ hz₀
    have hz₀c : z₀ ≠ c := by
      intro hcon
      exact hz₀.2 (Set.mem_singleton_iff.2 hcon)
    have htpos : 0 < ‖z₀ - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hz₀c)
    have htρ : ‖z₀ - c‖ < ρ := by
      rw [← dist_eq_norm]
      exact mem_ball.1 hz₀.1
    by_contra hne
    have hηpos : 0 < |u z₀ - G z₀| := abs_pos.2 (sub_ne_zero.2 hne)
    set η : ℝ := |u z₀ - G z₀| with hηdef
    set L₀ : ℝ := Real.log ρ - Real.log ‖z₀ - c‖ with hL₀def
    have hL₀pos : 0 < L₀ := by
      rw [hL₀def]
      exact sub_pos.2 (Real.log_lt_log htpos htρ)
    have h2CL : 0 ≤ 2 * C * L₀ := mul_nonneg (by linarith) hL₀pos.le
    set Kc : ℝ := (2 * C * L₀ + 1) / η with hKcdef
    have hKcpos : 0 < Kc := by
      rw [hKcdef]
      exact div_pos (by linarith) hηpos
    set δ : ℝ := min (‖z₀ - c‖ / 2) (ρ * Real.exp (-Kc)) with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]
      exact lt_min (by linarith) (by positivity)
    have hδt : δ < ‖z₀ - c‖ := by
      rw [hδdef]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδρ : δ < ρ := by
      have h1 : δ ≤ ρ * Real.exp (-Kc) := by rw [hδdef]; exact min_le_right _ _
      have h2 : Real.exp (-Kc) < 1 := Real.exp_lt_one_iff.2 (by linarith)
      have h3 : ρ * Real.exp (-Kc) < ρ * 1 := mul_lt_mul_of_pos_left h2 hρ
      linarith
    have hz₀A : z₀ ∈ ball c ρ \ closedBall c δ := by
      constructor
      · exact hz₀.1
      · intro hcon
        have h := mem_closedBall.1 hcon
        rw [dist_eq_norm] at h
        linarith
    have hbound := key δ hδpos hδρ z₀ hz₀A
    -- `Kc ≤ log ρ - log δ`, so the comparison constant is at most `2C/Kc`.
    have hlogδ : Kc ≤ Real.log ρ - Real.log δ := by
      have h1 : Real.log δ ≤ Real.log (ρ * Real.exp (-Kc)) := by
        apply Real.log_le_log hδpos
        rw [hδdef]
        exact min_le_right _ _
      rw [Real.log_mul hρ.ne' (Real.exp_ne_zero _), Real.log_exp] at h1
      linarith
    have hstep1 : 2 * C / (Real.log ρ - Real.log δ) ≤ 2 * C / Kc :=
      div_le_div_of_nonneg_left (by linarith) hKcpos hlogδ
    have hstep2 : 2 * C / (Real.log ρ - Real.log δ) * L₀ ≤ 2 * C / Kc * L₀ :=
      mul_le_mul_of_nonneg_right hstep1 hL₀pos.le
    have hne1 : (0 : ℝ) < 2 * C * L₀ + 1 := by linarith
    have hstep3 : 2 * C / Kc * L₀ < η := by
      have heq2 : 2 * C / Kc * L₀ = 2 * C * L₀ * η / (2 * C * L₀ + 1) := by
        rw [hKcdef]
        field_simp
      rw [heq2, div_lt_iff₀ hne1]
      nlinarith [hηpos, h2CL]
    rw [← hηdef, ← hL₀def] at hbound
    linarith
  -- `G` agrees with `u` on the whole punctured disk.
  have hGu : Set.EqOn G u (ball c r \ {c}) := by
    intro x hx
    by_cases hxρ : x ∈ ball c ρ
    · exact (claimA x ⟨hxρ, hx.2⟩).symm
    · exact hGoff x hxρ
  refine ⟨G, ?_, hGu⟩
  -- `G` is harmonic on the full disk: near the centre it is the Poisson solution,
  -- elsewhere it agrees with `u` on an open set.
  intro z hz
  by_cases hzρ : z ∈ ball c ρ
  · exact hGharm z hzρ
  · have hzc : z ∉ ({c} : Set ℂ) := by
      intro hcon
      rw [Set.mem_singleton_iff] at hcon
      apply hzρ
      rw [hcon]
      exact mem_ball_self hρ
    have hzmem : z ∈ ball c r \ {c} := ⟨hz, hzc⟩
    have hopen : IsOpen (ball c r \ {c}) := isOpen_ball.sdiff isClosed_singleton
    have heq : G =ᶠ[𝓝 z] u := eventuallyEq_of_mem (hopen.mem_nhds hzmem) hGu
    rw [harmonicAt_congr_nhds heq]
    exact hu z hzmem

/-- **Harnack's inequality** on concentric balls: a nonnegative harmonic
function on `ball c (2r)` satisfies the two-sided bound
`h c / 3 ≤ h z ≤ 3 * h c` on `ball c r`. -/
theorem harnack_inequality_ball {h : ℂ → ℝ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hh : HarmonicOnNhd h (ball c (2 * r)))
    (hpos : ∀ z ∈ ball c (2 * r), 0 ≤ h z) :
    ∀ z ∈ ball c r, h c / 3 ≤ h z ∧ h z ≤ 3 * h c := by
  intro z hz
  have hdr : dist z c < r := mem_ball.1 hz
  have hdnn : (0 : ℝ) ≤ dist z c := dist_nonneg
  -- The radius `ρ`: at least `3r/2` (so `ρ < 2r`) and at least `2 * dist z c` (constant `3`).
  set ρ : ℝ := max (3 * r / 2) (2 * dist z c) with hρdef
  have hρpos : 0 < ρ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hρlt : ρ < 2 * r := max_lt (by linarith) (by linarith)
  have hdρ : dist z c < ρ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have h2d : 2 * dist z c ≤ ρ := le_max_right _ _
  -- `h` is harmonic on `closedBall c ρ ⊆ ball c (2r)` and `z` is interior.
  have hsub : closedBall c ρ ⊆ ball c (2 * r) := closedBall_subset_ball hρlt
  have hhρ : HarmonicOnNhd h (closedBall c ρ) := hh.mono hsub
  have hzball : z ∈ ball c ρ := mem_ball.2 hdρ
  -- Poisson representation of `h z` and mean value at the center.
  have hrepr : Real.circleAverage (poissonKernel c z • h) c ρ = h z :=
    InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul hhρ hzball
  have hmean : Real.circleAverage h c ρ = h c :=
    InnerProductSpace.HarmonicOnNhd.circleAverage_eq (R := ρ) (c := c) (f := h)
      (by rwa [abs_of_pos hρpos])
  -- Two-sided Poisson-kernel bound on `sphere c ρ` from `ρ ≥ 2 * dist z c`.
  have hkerbd : ∀ w ∈ sphere c ρ,
      (1 : ℝ) / 3 ≤ poissonKernel c z w ∧ poissonKernel c z w ≤ 3 := by
    intro w hw
    have hker : poissonKernel c z w = ((w - c + (z - c)) / ((w - c) - (z - c))).re := by
      rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
        herglotzRieszKernel_def]
    constructor
    · rw [hker]
      refine le_trans ?_ (le_re_herglotzRieszKernel hw hzball)
      rw [← dist_eq_norm,
        div_le_div_iff₀ (by norm_num) (by linarith : (0 : ℝ) < ρ + dist z c)]
      linarith
    · rw [hker]
      refine le_trans (re_herglotzRieszKernel_le hw hzball) ?_
      rw [← dist_eq_norm, div_le_iff₀ (by linarith : (0 : ℝ) < ρ - dist z c)]
      linarith
  -- Continuity / integrability of the integrands on the circle.
  have hcont_h_sph : ContinuousOn h (sphere c ρ) :=
    hhρ.continuousOn.mono sphere_subset_closedBall
  have hkcont : ContinuousOn (fun w => poissonKernel c z w * h w) (sphere c ρ) := by
    apply ContinuousOn.mul ?_ hcont_h_sph
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    apply Complex.continuous_re.comp_continuousOn
    rw [herglotzRieszKernel_fun_def]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro w hw
    have hwn : ‖w - c‖ = ρ := by rw [← dist_eq_norm]; simpa using (mem_sphere.1 hw)
    intro hcontra
    have hwz : w - c = z - c := by linear_combination (norm := ring_nf) hcontra
    rw [hwz, ← dist_eq_norm] at hwn
    linarith
  have hkci : CircleIntegrable (fun w => poissonKernel c z w * h w) c ρ :=
    hkcont.circleIntegrable hρpos.le
  have h3ci : CircleIntegrable (fun w => 3 * h w) c ρ :=
    (continuousOn_const.mul hcont_h_sph).circleIntegrable hρpos.le
  have hthirdci : CircleIntegrable (fun w => (1 : ℝ) / 3 * h w) c ρ :=
    (continuousOn_const.mul hcont_h_sph).circleIntegrable hρpos.le
  -- `h ≥ 0` on the circle, so the kernel bounds transfer to the integrands.
  have hsph_pos : ∀ w ∈ sphere c ρ, 0 ≤ h w := fun w hw =>
    hpos w (hsub (sphere_subset_closedBall hw))
  have hpt_up : ∀ w ∈ sphere c |ρ|, poissonKernel c z w * h w ≤ 3 * h w := by
    intro w hw
    rw [abs_of_pos hρpos] at hw
    obtain ⟨-, hk3⟩ := hkerbd w hw
    have hw0 := hsph_pos w hw
    nlinarith
  have hpt_lo : ∀ w ∈ sphere c |ρ|, (1 : ℝ) / 3 * h w ≤ poissonKernel c z w * h w := by
    intro w hw
    rw [abs_of_pos hρpos] at hw
    obtain ⟨hk1, -⟩ := hkerbd w hw
    have hw0 := hsph_pos w hw
    nlinarith
  -- Upper bound: `h z ≤ 3 * h c`.
  have hup : h z ≤ 3 * h c := by
    calc h z = Real.circleAverage (poissonKernel c z • h) c ρ := hrepr.symm
      _ = Real.circleAverage (fun w => poissonKernel c z w * h w) c ρ := by
          apply Real.circleAverage_congr_sphere; intro w _; simp [smul_eq_mul]
      _ ≤ Real.circleAverage (fun w => 3 * h w) c ρ :=
          Real.circleAverage_mono hkci h3ci hpt_up
      _ = 3 * Real.circleAverage h c ρ := by
          rw [show (fun w => (3 : ℝ) * h w) = (fun w => (3 : ℝ) • h w) by
            simp [smul_eq_mul], Real.circleAverage_fun_smul, smul_eq_mul]
      _ = 3 * h c := by rw [hmean]
  -- Lower bound: `h c / 3 ≤ h z`.
  have hlo : h c / 3 ≤ h z := by
    have hkey : (1 : ℝ) / 3 * h c ≤ h z := by
      calc (1 : ℝ) / 3 * h c = (1 : ℝ) / 3 * Real.circleAverage h c ρ := by rw [hmean]
        _ = Real.circleAverage (fun w => (1 : ℝ) / 3 * h w) c ρ := by
            rw [show (fun w => (1 : ℝ) / 3 * h w) = (fun w => ((1 : ℝ) / 3) • h w) by
              simp [smul_eq_mul], Real.circleAverage_fun_smul, smul_eq_mul]
        _ ≤ Real.circleAverage (fun w => poissonKernel c z w * h w) c ρ :=
            Real.circleAverage_mono hthirdci hkci hpt_lo
        _ = Real.circleAverage (poissonKernel c z • h) c ρ := by
            apply Real.circleAverage_congr_sphere; intro w _; simp [smul_eq_mul]
        _ = h z := hrepr
    linarith
  exact ⟨hlo, hup⟩

/-- **Strong maximum principle** for subharmonic functions: at an interior
global maximum, a subharmonic function is locally constant. -/
theorem SubharmonicOn.eventually_eq_of_le {u : ℂ → ℝ} {U : Set ℂ} {c : ℂ}
    (hU : IsOpen U) (hu : SubharmonicOn u U) (hc : c ∈ U)
    (hmax : ∀ z ∈ U, u z ≤ u c) : ∀ᶠ z in 𝓝 c, u z = u c := by
  obtain ⟨hcont, hmv⟩ := hu
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hc)
  have key : ∀ z ∈ Metric.ball c r, u z = u c := by
    intro z hz
    rcases eq_or_ne z c with rfl | hne
    · rfl
    by_contra hne2
    -- The circle through `z` centred at `c`.
    set s : ℝ := dist z c with hs
    have hspos : 0 < s := by rw [hs]; exact dist_pos.2 hne
    have hslt : s < r := by rw [hs]; exact Metric.mem_ball.1 hz
    have hballs : Metric.closedBall c s ⊆ U :=
      (Metric.closedBall_subset_closedBall hslt.le).trans hball
    have hsphs : Metric.sphere c s ⊆ U := Metric.sphere_subset_closedBall.trans hballs
    have hzsph : z ∈ Metric.sphere c s := Metric.mem_sphere.2 hs.symm
    have hlt : u z < u c := lt_of_le_of_ne (hmax z (hsphs hzsph)) hne2
    -- The circle average equals the maximal value `u c`.
    have hci : CircleIntegrable u c s := (hcont.mono hsphs).circleIntegrable hspos.le
    have h1 : u c ≤ Real.circleAverage u c s := hmv c hc s hspos hballs
    have h2 : Real.circleAverage u c s ≤ u c := by
      apply Real.circleAverage_mono_on_of_le_circle hci
      intro x hx
      rw [abs_of_pos hspos] at hx
      exact hmax x (hsphs hx)
    have havg : Real.circleAverage u c s = u c := le_antisymm h2 h1
    -- The angular deficiency `g θ = u c - u (circleMap c s θ)`: continuous, nonneg, integral 0.
    set g : ℝ → ℝ := fun θ => u c - u (circleMap c s θ) with hg
    have hUmem : ∀ θ : ℝ, circleMap c s θ ∈ U :=
      fun θ => hsphs (circleMap_mem_sphere c hspos.le θ)
    have hucont : Continuous fun θ : ℝ => u (circleMap c s θ) := by
      rw [continuous_iff_continuousAt]
      intro θ
      exact (hcont.continuousAt (hU.mem_nhds (hUmem θ))).comp
        (continuous_circleMap c s).continuousAt
    have hgcont : Continuous g := continuous_const.sub hucont
    have hgnonneg : ∀ θ, 0 ≤ g θ := fun θ => sub_nonneg.2 (hmax _ (hUmem θ))
    have hcint : IntervalIntegrable (fun θ : ℝ => u (circleMap c s θ)) volume 0 (2 * π) := hci
    have hIint : (∫ θ in (0:ℝ)..(2 * π), u (circleMap c s θ)) = 2 * π * u c := by
      have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
      have hdef : Real.circleAverage u c s
          = (2 * π)⁻¹ • ∫ θ in (0:ℝ)..(2 * π), u (circleMap c s θ) :=
        Real.circleAverage_def
      rw [havg] at hdef
      rw [hdef, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ h2pi, one_mul]
    have hIg : (∫ θ in (0:ℝ)..(2 * π), g θ) = 0 := by
      simp only [hg]
      rw [intervalIntegral.integral_sub intervalIntegrable_const hcint,
        intervalIntegral.integral_const, hIint]
      simp only [sub_zero, smul_eq_mul]
      ring
    -- A parameter `θ₀ ∈ [0, 2π)` where the deficiency is positive.
    obtain ⟨θz, hθz⟩ : ∃ θ : ℝ, circleMap c s θ = z := by
      have hz' : z ∈ Set.range (circleMap c s) := by
        rw [range_circleMap, abs_of_pos hspos]
        exact hzsph
      exact hz'
    have hper : Function.Periodic g (2 * π) := by
      intro θ
      simp only [hg]
      rw [periodic_circleMap c s θ]
    obtain ⟨θ₀, hθ₀mem, hθ₀eq⟩ := hper.exists_mem_Ico₀ Real.two_pi_pos θz
    have hgθ₀ : 0 < g θ₀ := by
      rw [← hθ₀eq]
      simp only [hg]
      rw [hθz]
      linarith
    -- The deficiency stays positive on a small interval to the right of `θ₀`.
    have hopen : IsOpen {θ : ℝ | 0 < g θ} := isOpen_lt continuous_const hgcont
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.1 hopen θ₀ hgθ₀
    set b : ℝ := min (θ₀ + δ) (2 * π) with hb
    have hθ₀lt2π : θ₀ < 2 * π := hθ₀mem.2
    have hθ₀nonneg : 0 ≤ θ₀ := hθ₀mem.1
    have hθ₀b : θ₀ < b := lt_min (by linarith) hθ₀lt2π
    have hb2π : b ≤ 2 * π := min_le_right _ _
    have hposIoo : ∀ x ∈ Set.Ioo θ₀ b, 0 < g x := by
      intro x hx
      have hxball : x ∈ Metric.ball θ₀ δ := by
        rw [Real.ball_eq_Ioo]
        refine ⟨by linarith [hx.1], ?_⟩
        have := lt_of_lt_of_le hx.2 (min_le_left (θ₀ + δ) (2 * π))
        linarith
      exact hδsub hxball
    -- Split the zero integral into three nonnegative pieces, the middle strictly positive.
    have hi1 : IntervalIntegrable g volume 0 θ₀ := hgcont.intervalIntegrable _ _
    have hi2 : IntervalIntegrable g volume θ₀ b := hgcont.intervalIntegrable _ _
    have hi3 : IntervalIntegrable g volume b (2 * π) := hgcont.intervalIntegrable _ _
    have hsplit : (∫ θ in (0:ℝ)..θ₀, g θ) + (∫ θ in θ₀..b, g θ)
        + (∫ θ in b..(2 * π), g θ) = ∫ θ in (0:ℝ)..(2 * π), g θ := by
      rw [intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
      exact intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3
    have hn1 : 0 ≤ ∫ θ in (0:ℝ)..θ₀, g θ :=
      intervalIntegral.integral_nonneg hθ₀nonneg fun x _ => hgnonneg x
    have hn3 : 0 ≤ ∫ θ in b..(2 * π), g θ :=
      intervalIntegral.integral_nonneg hb2π fun x _ => hgnonneg x
    have hp2 : 0 < ∫ θ in θ₀..b, g θ :=
      intervalIntegral.intervalIntegral_pos_of_pos_on hi2 hposIoo hθ₀b
    rw [hIg] at hsplit
    linarith
  filter_upwards [Metric.ball_mem_nhds c hr] with z hz using key z hz

end RiemannDynamics
