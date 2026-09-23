/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.Perron.HarmonicTransfer
import RiemannDynamics.Uniformization.SphereManifold
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Harmonic and subharmonic functions on Riemann surfaces

Chart-local potential theory on a one-dimensional complex-analytic manifold:
a real function is harmonic (subharmonic) at a point when its reading in the
preferred chart is harmonic (subharmonic on a small ball). By the conformal
invariance bricks of `HarmonicTransfer.lean`, these notions agree with the
readings in every chart of the maximal analytic atlas, so all local plane
results transfer to the surface.

## Main definitions

* `MHarmonicAt`, `MHarmonicOn` — harmonicity at a point / on a set, read in
  the preferred chart;
* `MSubharmonicAt`, `MSubharmonicOn` — subharmonicity, read in the preferred
  chart on a small ball.

## Main statements

* `mharmonicAt_iff_of_mem_maximalAtlas`, `msubharmonicAt_iff_of_mem_maximalAtlas`
  — chart independence;
* `MSubharmonicOn.max` — stability under pointwise maximum;
* `MSubharmonicOn.apply_le_of_isMaxOn` (via `eventually_eq`) and
  `MSubharmonicOn.eq_of_le` — the strong maximum principle on a connected
  surface;
* `mharmonicOn_of_monotone_tendsto` — the Harnack monotone-limit principle.
-/

open Metric InnerProductSpace Topology Filter TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- A real function on a Riemann surface is harmonic at `x` when its reading
in the preferred chart at `x` is harmonic at the chart image of `x`. -/
def MHarmonicAt (u : M → ℝ) (x : M) : Prop :=
  HarmonicAt (u ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)

/-- Harmonicity on a set: harmonicity at every point of the set. -/
def MHarmonicOn (u : M → ℝ) (s : Set M) : Prop := ∀ x ∈ s, MHarmonicAt u x

/-- A real function on a Riemann surface is subharmonic at `x` when its
reading in the preferred chart at `x` is subharmonic on some ball around the
chart image of `x` inside the chart target. -/
def MSubharmonicAt (v : M → ℝ) (x : M) : Prop :=
  ∃ r > 0, ball (chartAt ℂ x x) r ⊆ (chartAt ℂ x).target ∧
    SubharmonicOn (v ∘ (chartAt ℂ x).symm) (ball (chartAt ℂ x x) r)

/-- Subharmonicity on a set: subharmonicity at every point of the set. -/
def MSubharmonicOn (v : M → ℝ) (s : Set M) : Prop := ∀ x ∈ s, MSubharmonicAt v x

variable [IsManifold 𝓘(ℂ) ω M]

/-! ## Chart independence -/

/-- Harmonicity can be read in any chart of the maximal analytic atlas. -/
theorem mharmonicAt_iff_of_mem_maximalAtlas {u : M → ℝ} {x : M}
    {e : OpenPartialHomeomorph M ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω M)
    (hx : x ∈ e.source) :
    MHarmonicAt u x ↔ HarmonicAt (u ∘ e.symm) (e x) := by
  -- Generic one-directional transfer between two charts of the maximal atlas.
  have key : ∀ f g : OpenPartialHomeomorph M ℂ,
      f ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω M →
      g ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω M →
      x ∈ f.source → x ∈ g.source →
      HarmonicAt (u ∘ f.symm) (f x) → HarmonicAt (u ∘ g.symm) (g x) := by
    intro f g hf hg hxf hxg hH
    -- The transition map from `g`-coordinates to `f`-coordinates is analytic.
    have hcd : ContDiffOn ℂ ω (↑(g.symm ≫ₕ f)) (g.symm ≫ₕ f).source := by
      have h1 := (IsManifold.compatible_of_mem_maximalAtlas hg hf).1
      simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
        Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ] at h1
      exact h1
    have hsrc : (g.symm ≫ₕ f).source = g.target ∩ ↑g.symm ⁻¹' f.source := by
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    have hgx_src : g x ∈ (g.symm ≫ₕ f).source := by
      rw [hsrc]
      refine ⟨g.map_source hxg, ?_⟩
      rw [Set.mem_preimage, g.left_inv hxg]
      exact hxf
    have hnhds : (g.symm ≫ₕ f).source ∈ 𝓝 (g x) :=
      (g.symm ≫ₕ f).open_source.mem_nhds hgx_src
    have han : AnalyticAt ℂ (↑(g.symm ≫ₕ f)) (g x) :=
      (hcd.differentiableOn (by simp)).analyticAt hnhds
    -- The transition sends `g x` to `f x`.
    have hval : (↑(g.symm ≫ₕ f) : ℂ → ℂ) (g x) = f x := by
      calc (↑(g.symm ≫ₕ f) : ℂ → ℂ) (g x) = f (g.symm (g x)) := rfl
        _ = f x := by rw [g.left_inv hxg]
    have hHval : HarmonicAt (u ∘ ↑f.symm) ((↑(g.symm ≫ₕ f) : ℂ → ℂ) (g x)) := by
      rw [hval]; exact hH
    have hcomp : HarmonicAt ((u ∘ ↑f.symm) ∘ ↑(g.symm ≫ₕ f)) (g x) :=
      harmonicAt_comp_analyticAt hHval han
    -- Near `g x` the composite reading agrees with the `g`-chart reading.
    have heq : (u ∘ ↑f.symm) ∘ ↑(g.symm ≫ₕ f) =ᶠ[𝓝 (g x)] u ∘ ↑g.symm := by
      filter_upwards [hnhds] with w hw
      rw [hsrc] at hw
      calc ((u ∘ ↑f.symm) ∘ ↑(g.symm ≫ₕ f)) w = u (f.symm (f (g.symm w))) := rfl
        _ = u (g.symm w) := by rw [f.left_inv hw.2]
    exact (harmonicAt_congr_nhds heq).mp hcomp
  constructor
  · intro hH
    exact key (chartAt ℂ x) e (IsManifold.chart_mem_maximalAtlas x) he
      (mem_chart_source ℂ x) hx hH
  · intro hH
    exact key e (chartAt ℂ x) he (IsManifold.chart_mem_maximalAtlas x) hx
      (mem_chart_source ℂ x) hH

/-- Subharmonicity can be read in any chart of the maximal analytic atlas. -/
theorem msubharmonicAt_iff_of_mem_maximalAtlas {v : M → ℝ} {x : M}
    {e : OpenPartialHomeomorph M ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω M)
    (hx : x ∈ e.source) :
    MSubharmonicAt v x ↔
      ∃ r > 0, ball (e x) r ⊆ e.target ∧
        SubharmonicOn (v ∘ e.symm) (ball (e x) r) := by
  -- Subharmonicity restricts along inclusions and transports across equal readings.
  have transfer : ∀ (F G : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F U → W ⊆ U →
      Set.EqOn F G W → SubharmonicOn G W := by
    intro F G U W hF hWU hFG
    refine ⟨(hF.1.mono hWU).congr hFG.symm, ?_⟩
    intro c hc ρ hρ hb
    have h1 : G c = F c := (hFG hc).symm
    have h2 : Real.circleAverage F c ρ = Real.circleAverage G c ρ := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hρ] at hz
      exact hFG (hb (sphere_subset_closedBall hz))
    rw [h1, ← h2]
    exact hF.2 c (hWU hc) ρ hρ (hb.trans hWU)
  -- Generic one-directional transfer between two charts of the maximal atlas.
  have key : ∀ f g : OpenPartialHomeomorph M ℂ,
      f ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω M →
      g ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω M →
      x ∈ f.source → x ∈ g.source →
      (∃ r > 0, ball (f x) r ⊆ f.target ∧ SubharmonicOn (v ∘ f.symm) (ball (f x) r)) →
      ∃ r > 0, ball (g x) r ⊆ g.target ∧ SubharmonicOn (v ∘ g.symm) (ball (g x) r) := by
    intro f g hf hg hxf hxg hex
    obtain ⟨r, hr, -, hsub⟩ := hex
    -- The transition map from `g`-coordinates to `f`-coordinates is biholomorphic.
    have hcd1 : ContDiffOn ℂ ω (↑(g.symm ≫ₕ f)) (g.symm ≫ₕ f).source := by
      have h1 := (IsManifold.compatible_of_mem_maximalAtlas hg hf).1
      simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
        Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ] at h1
      exact h1
    have hcd2 : ContDiffOn ℂ ω (↑(g.symm ≫ₕ f).symm) (g.symm ≫ₕ f).target := by
      have h2 := (IsManifold.compatible_of_mem_maximalAtlas hg hf).2
      simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
        Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ] at h2
      exact h2
    have hsrc : (g.symm ≫ₕ f).source = g.target ∩ ↑g.symm ⁻¹' f.source := by
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    have hgx_src : g x ∈ (g.symm ≫ₕ f).source := by
      rw [hsrc]
      refine ⟨g.map_source hxg, ?_⟩
      rw [Set.mem_preimage, g.left_inv hxg]
      exact hxf
    have hval : (↑(g.symm ≫ₕ f) : ℂ → ℂ) (g x) = f x := by
      calc (↑(g.symm ≫ₕ f) : ℂ → ℂ) (g x) = f (g.symm (g x)) := rfl
        _ = f x := by rw [g.left_inv hxg]
    have hfx_tgt : f x ∈ (g.symm ≫ₕ f).target := by
      have h := (g.symm ≫ₕ f).map_source hgx_src
      rwa [hval] at h
    -- Transport subharmonicity through the transition map.
    have hsub' : SubharmonicOn (v ∘ ↑f.symm) (ball (f x) r ∩ (g.symm ≫ₕ f).target) :=
      transfer _ _ _ _ hsub Set.inter_subset_left (fun _ _ => rfl)
    have hcomp : SubharmonicOn ((v ∘ ↑f.symm) ∘ ↑(g.symm ≫ₕ f))
        ((g.symm ≫ₕ f).source ∩
          ↑(g.symm ≫ₕ f) ⁻¹' (ball (f x) r ∩ (g.symm ≫ₕ f).target)) :=
      subharmonicOn_comp_biholo (g.symm ≫ₕ f) (hcd1.differentiableOn (by simp))
        (hcd2.differentiableOn (by simp)) hsub' Set.inter_subset_right
    -- The transported domain is an open neighbourhood of `g x`; shrink to a ball.
    have hSopen : IsOpen ((g.symm ≫ₕ f).source ∩
        ↑(g.symm ≫ₕ f) ⁻¹' (ball (f x) r ∩ (g.symm ≫ₕ f).target)) :=
      (g.symm ≫ₕ f).isOpen_inter_preimage (isOpen_ball.inter (g.symm ≫ₕ f).open_target)
    have hgx_S : g x ∈ (g.symm ≫ₕ f).source ∩
        ↑(g.symm ≫ₕ f) ⁻¹' (ball (f x) r ∩ (g.symm ≫ₕ f).target) := by
      refine ⟨hgx_src, ?_⟩
      rw [Set.mem_preimage, hval]
      exact ⟨mem_ball_self hr, hfx_tgt⟩
    obtain ⟨ε, hε, hεball⟩ := Metric.isOpen_iff.mp hSopen (g x) hgx_S
    refine ⟨ε, hε, ?_, ?_⟩
    · intro w hw
      have hw_src : w ∈ (g.symm ≫ₕ f).source := (hεball hw).1
      rw [hsrc] at hw_src
      exact hw_src.1
    · refine transfer _ _ _ _ hcomp hεball ?_
      intro w hw
      have hw_src : w ∈ (g.symm ≫ₕ f).source := (hεball hw).1
      rw [hsrc] at hw_src
      calc ((v ∘ ↑f.symm) ∘ ↑(g.symm ≫ₕ f)) w = v (f.symm (f (g.symm w))) := rfl
        _ = v (g.symm w) := by rw [f.left_inv hw_src.2]
  constructor
  · intro hH
    exact key (chartAt ℂ x) e (IsManifold.chart_mem_maximalAtlas x) he
      (mem_chart_source ℂ x) hx hH
  · intro hH
    exact key e (chartAt ℂ x) he (IsManifold.chart_mem_maximalAtlas x) hx
      (mem_chart_source ℂ x) hH

/-! ## Basic stability -/

omit [IsManifold 𝓘(ℂ) ω M] in
/-- A function harmonic at a point of a surface is subharmonic there: harmonicity of the chart
reading propagates to a whole ball inside the chart target, and harmonic functions are
subharmonic. -/
theorem MHarmonicAt.msubharmonicAt {u : M → ℝ} {x : M} (hu : MHarmonicAt u x) :
    MSubharmonicAt u x := by
  have hu' : HarmonicAt (u ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := hu
  have hev : ∀ᶠ y in 𝓝 (chartAt ℂ x x),
      HarmonicAt (u ∘ (chartAt ℂ x).symm) y ∧ y ∈ (chartAt ℂ x).target :=
    hu'.eventually.and ((chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  exact ⟨r, hr, fun y hy => (hball y hy).2,
    HarmonicOnNhd.subharmonicOn fun y hy => (hball y hy).1⟩

/- 2 -/

omit [IsManifold 𝓘(ℂ) ω M] in
/-- A function subharmonic at a point of a surface is continuous there: its chart reading is
continuous on a ball around the chart image, and the chart itself is continuous at the point. -/
theorem MSubharmonicAt.continuousAt {v : M → ℝ} {x : M}
    (hv : MSubharmonicAt v x) : ContinuousAt v x := by
  obtain ⟨r, hr, -, hsh⟩ := hv
  have hc1 : ContinuousAt (v ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) :=
    hsh.1.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hc2 : ContinuousAt (chartAt ℂ x) x :=
    (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
  refine (hc1.comp hc2).congr_of_eventuallyEq ?_
  filter_upwards [(chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)] with y hy
  simp only [Function.comp_apply, (chartAt ℂ x).left_inv hy]

/- 3 -/

omit [IsManifold 𝓘(ℂ) ω M] in
/-- A function harmonic at a point of a surface is continuous there: its chart reading is
continuous at the chart image, and the chart itself is continuous at the point. -/
theorem MHarmonicAt.continuousAt {u : M → ℝ} {x : M} (hu : MHarmonicAt u x) :
    ContinuousAt u x := by
  have hu' : HarmonicAt (u ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := hu
  have hc1 : ContinuousAt (u ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := hu'.1.continuousAt
  have hc2 : ContinuousAt (chartAt ℂ x) x :=
    (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
  refine (hc1.comp hc2).congr_of_eventuallyEq ?_
  filter_upwards [(chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)] with y hy
  simp only [Function.comp_apply, (chartAt ℂ x).left_inv hy]

/- 4 -/

omit [IsManifold 𝓘(ℂ) ω M] in
/-- The pointwise maximum of two subharmonic functions is subharmonic. -/
theorem MSubharmonicAt.max {v w : M → ℝ} {x : M} (hv : MSubharmonicAt v x)
    (hw : MSubharmonicAt w x) : MSubharmonicAt (fun y => max (v y) (w y)) x := by
  obtain ⟨r₁, hr₁, hsub₁, hsh₁⟩ := hv
  obtain ⟨r₂, hr₂, -, hsh₂⟩ := hw
  have hmono : ∀ (f : ℂ → ℝ) (U V : Set ℂ),
      SubharmonicOn f U → V ⊆ U → SubharmonicOn f V :=
    fun f U V hf hVU =>
      ⟨hf.1.mono hVU, fun c hc ρ hρ hball => hf.2 c (hVU hc) ρ hρ (hball.trans hVU)⟩
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂,
    (ball_subset_ball (min_le_left r₁ r₂)).trans hsub₁, ?_⟩
  exact subharmonicOn_max
    (hmono _ _ _ hsh₁ (ball_subset_ball (min_le_left r₁ r₂)))
    (hmono _ _ _ hsh₂ (ball_subset_ball (min_le_right r₁ r₂)))

/- 5 -/

omit [IsManifold 𝓘(ℂ) ω M] in
/-- The sum of two functions harmonic at a point of a surface is harmonic at that point, since
the chart reading of `u + v` is the sum of the chart readings. -/
theorem MHarmonicAt.add {u v : M → ℝ} {x : M} (hu : MHarmonicAt u x)
    (hv : MHarmonicAt v x) : MHarmonicAt (u + v) x := by
  have hu' : HarmonicAt (u ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := hu
  have hv' : HarmonicAt (v ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := hv
  exact hu'.add hv'

/- 6 -/

omit [IsManifold 𝓘(ℂ) ω M] in
/-- The negative of a function harmonic at a point of a surface is harmonic at that point. -/
theorem MHarmonicAt.neg {u : M → ℝ} {x : M} (hu : MHarmonicAt u x) :
    MHarmonicAt (-u) x := by
  have hu' : HarmonicAt (u ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := hu
  exact hu'.neg

/- 7 -/

omit [IsManifold 𝓘(ℂ) ω M] in
/-- Constant functions are harmonic at every point of a surface: their chart reading is again a
constant, which is harmonic in the plane. -/
theorem mharmonicAt_const {x : M} {a : ℝ} : MHarmonicAt (fun _ => a) x := by
  exact harmonicAt_const a

/- 8 -/

omit [IsManifold 𝓘(ℂ) ω M] in
/-- A subharmonic function minus a harmonic function is subharmonic. -/
theorem MSubharmonicAt.sub_mharmonicAt {v u : M → ℝ} {x : M}
    (hv : MSubharmonicAt v x) (hu : MHarmonicAt u x) :
    MSubharmonicAt (fun y => v y - u y) x := by
  obtain ⟨r₁, hr₁, hsub₁, hsh₁⟩ := hv
  have hu' : HarmonicAt (u ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := hu
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.eventually_nhds_iff_ball.mp hu'.eventually
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂,
    (ball_subset_ball (min_le_left r₁ r₂)).trans hsub₁, ?_⟩
  have hsh : SubharmonicOn (v ∘ (chartAt ℂ x).symm) (ball (chartAt ℂ x x) (min r₁ r₂)) :=
    ⟨hsh₁.1.mono (ball_subset_ball (min_le_left r₁ r₂)),
      fun c hc ρ hρ hball => hsh₁.2 c (ball_subset_ball (min_le_left r₁ r₂) hc) ρ hρ
        (hball.trans (ball_subset_ball (min_le_left r₁ r₂)))⟩
  have hh : HarmonicOnNhd (u ∘ (chartAt ℂ x).symm) (ball (chartAt ℂ x x) (min r₁ r₂)) :=
    fun y hy => hball₂ y (ball_subset_ball (min_le_right r₁ r₂) hy)
  have key : SubharmonicOn
      (fun z => (v ∘ (chartAt ℂ x).symm) z - (u ∘ (chartAt ℂ x).symm) z)
      (ball (chartAt ℂ x x) (min r₁ r₂)) := by
    obtain ⟨hfc, hfmv⟩ := hsh
    refine ⟨hfc.sub hh.continuousOn, ?_⟩
    intro c hc ρ hρ hsubB
    have hsphere : Metric.sphere c ρ ⊆ ball (chartAt ℂ x x) (min r₁ r₂) :=
      Metric.sphere_subset_closedBall.trans hsubB
    have hfci : CircleIntegrable (v ∘ (chartAt ℂ x).symm) c ρ :=
      (hfc.mono hsphere).circleIntegrable hρ.le
    have hhci : CircleIntegrable (u ∘ (chartAt ℂ x).symm) c ρ :=
      (hh.continuousOn.mono hsphere).circleIntegrable hρ.le
    rw [Real.circleAverage_fun_sub hfci hhci]
    have hhavg : Real.circleAverage (u ∘ (chartAt ℂ x).symm) c ρ =
        (u ∘ (chartAt ℂ x).symm) c := by
      apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
      rw [abs_of_pos hρ]
      exact hh.mono hsubB
    have hfavg : (v ∘ (chartAt ℂ x).symm) c ≤
        Real.circleAverage (v ∘ (chartAt ℂ x).symm) c ρ := hfmv c hc ρ hρ hsubB
    rw [hhavg]
    linarith
  exact key

/-! ## The strong maximum principle -/

omit [IsManifold 𝓘(ℂ) ω M] in
/-- At an interior global maximum, a subharmonic function on a surface is
locally constant. -/
theorem MSubharmonicAt.eventually_eq_of_le {v : M → ℝ} {x₀ : M} {s : Set M}
    (hs : IsOpen s) (hx₀ : x₀ ∈ s) (hv : MSubharmonicOn v s)
    (hmax : ∀ x ∈ s, v x ≤ v x₀) : ∀ᶠ x in 𝓝 x₀, v x = v x₀ := by
  obtain ⟨r, hr, hball, hsub⟩ := hv x₀ hx₀
  set e := chartAt ℂ x₀
  have hxsrc : x₀ ∈ e.source := mem_chart_source ℂ x₀
  have hcx : e.symm (e x₀) = x₀ := e.left_inv hxsrc
  -- The plane-side open set: the chart ball, intersected with the pullback of `s`.
  set U : Set ℂ := ball (e x₀) r ∩ (e.target ∩ e.symm ⁻¹' s)
  have hUopen : IsOpen U := isOpen_ball.inter (e.isOpen_inter_preimage_symm hs)
  have hcU : e x₀ ∈ U :=
    ⟨mem_ball_self hr, e.map_source hxsrc, by simpa [hcx] using hx₀⟩
  -- Subharmonicity restricts to `U ⊆ ball (e x₀) r`.
  have hsubU : SubharmonicOn (v ∘ e.symm) U :=
    ⟨hsub.1.mono Set.inter_subset_left,
      fun z hz ρ hρ hb => hsub.2 z hz.1 ρ hρ (hb.trans Set.inter_subset_left)⟩
  -- The chart image of `x₀` is an interior maximum of the plane reading.
  have hmaxU : ∀ z ∈ U, (v ∘ e.symm) z ≤ (v ∘ e.symm) (e x₀) := by
    intro z hz
    have hzs : e.symm z ∈ s := hz.2.2
    simpa [Function.comp_apply, hcx] using hmax _ hzs
  -- Plane strong maximum principle.
  have hev : ∀ᶠ w in 𝓝 (e x₀), (v ∘ e.symm) w = (v ∘ e.symm) (e x₀) :=
    SubharmonicOn.eventually_eq_of_le hUopen hsubU hcU hmaxU
  -- Transport back through the chart.
  have hcont : ContinuousAt e x₀ := e.continuousAt hxsrc
  have hev' : ∀ᶠ y in 𝓝 x₀, (v ∘ e.symm) (e y) = (v ∘ e.symm) (e x₀) :=
    hcont.eventually hev
  have hsrc : ∀ᶠ y in 𝓝 x₀, y ∈ e.source := e.open_source.eventually_mem hxsrc
  filter_upwards [hev', hsrc] with y hy hysrc
  have hy' : v y = v (e.symm (e x₀)) := by
    simpa [Function.comp_apply, e.left_inv hysrc] using hy
  rw [hy', hcx]

omit [IsManifold 𝓘(ℂ) ω M] in
/-- **Strong maximum principle**: a subharmonic function on a connected
surface attaining a global maximum is constant. -/
theorem MSubharmonicOn.eq_of_le [ConnectedSpace M] {v : M → ℝ} {x₀ : M}
    (hv : MSubharmonicOn v Set.univ) (hmax : ∀ x, v x ≤ v x₀) :
    ∀ x, v x = v x₀ := by
  have hcont : Continuous v :=
    continuous_iff_continuousAt.mpr fun x => (hv x (Set.mem_univ x)).continuousAt
  have hopen : IsOpen {x | v x = v x₀} := by
    rw [isOpen_iff_mem_nhds]
    intro a ha
    have hmaxa : ∀ x ∈ (Set.univ : Set M), v x ≤ v a :=
      fun x _ => (hmax x).trans_eq ha.symm
    have hev := MSubharmonicAt.eventually_eq_of_le isOpen_univ (Set.mem_univ a) hv hmaxa
    exact eventually_iff.mp (hev.mono fun x hx => hx.trans ha)
  have hclosed : IsClosed {x | v x = v x₀} := isClosed_eq hcont continuous_const
  have huniv : {x | v x = v x₀} = Set.univ :=
    IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨x₀, rfl⟩
  exact fun x => Set.eq_univ_iff_forall.mp huniv x

/-! ## The Harnack monotone-limit principle -/

/-- **Harnack's principle** on a surface: the pointwise limit of a monotone,
pointwise-bounded sequence of harmonic functions is harmonic. -/
theorem mharmonicOn_of_monotone_tendsto {s : Set M} (hs : IsOpen s)
    {V : ℕ → M → ℝ} {Vlim : M → ℝ}
    (hV : ∀ n, MHarmonicOn (V n) s)
    (hmono : ∀ x ∈ s, Monotone (fun n => V n x))
    (htends : ∀ x ∈ s, Tendsto (fun n => V n x) atTop (𝓝 (Vlim x))) :
    MHarmonicOn Vlim s := by
  intro x hx
  -- Choose a ball around the chart image of `x` inside the chart target whose
  -- preimage under the inverse chart lies in `s`.
  have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hopen : IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' s) :=
    (chartAt ℂ x).isOpen_inter_preimage_symm hs
  have hmem : chartAt ℂ x x ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' s := by
    refine ⟨(chartAt ℂ x).map_source hxsrc, ?_⟩
    rw [Set.mem_preimage, (chartAt ℂ x).left_inv hxsrc]
    exact hx
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.1 hopen _ hmem
  -- Points of the ball read back into `s`.
  have hmem' : ∀ z ∈ ball (chartAt ℂ x x) ρ, (chartAt ℂ x).symm z ∈ s := by
    intro z hz
    have h := (hρsub hz).2
    rwa [Set.mem_preimage] at h
  -- Transport: the reading in `x`'s chart of any function harmonic on `s` is
  -- harmonic at every point of the ball, via the analytic transition map to
  -- the preferred chart of the read-back point.
  have htrans : ∀ u : M → ℝ, MHarmonicOn u s →
      ∀ w ∈ ball (chartAt ℂ x x) ρ, HarmonicAt (u ∘ (chartAt ℂ x).symm) w := by
    intro u hu w hw
    have hwt : w ∈ (chartAt ℂ x).target := (hρsub hw).1
    have hws : (chartAt ℂ x).symm w ∈ s := hmem' w hw
    -- Harmonicity of `u` read in the preferred chart at the read-back point.
    have hMH : HarmonicAt (u ∘ (chartAt ℂ ((chartAt ℂ x).symm w)).symm)
        (chartAt ℂ ((chartAt ℂ x).symm w) ((chartAt ℂ x).symm w)) := hu _ hws
    -- The transition map between the two charts belongs to the analytic groupoid.
    have hcompat : (chartAt ℂ x).symm ≫ₕ chartAt ℂ ((chartAt ℂ x).symm w) ∈
        contDiffGroupoid ω 𝓘(ℂ) :=
      StructureGroupoid.compatible_of_mem_maximalAtlas
        (StructureGroupoid.chart_mem_maximalAtlas (contDiffGroupoid ω 𝓘(ℂ)) x)
        (StructureGroupoid.chart_mem_maximalAtlas (contDiffGroupoid ω 𝓘(ℂ)) _)
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hcompat
    have hprop := hcompat.1
    simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
      Set.inter_univ] at hprop
    -- `w` lies in the source of the transition map.
    have hwτ :
        w ∈ ((chartAt ℂ x).symm ≫ₕ chartAt ℂ ((chartAt ℂ x).symm w)).source := by
      rw [OpenPartialHomeomorph.trans_source, (chartAt ℂ x).symm_source]
      exact ⟨hwt, by rw [Set.mem_preimage]; exact mem_chart_source ℂ _⟩
    -- The transition map is analytic at `w`.
    have hana : AnalyticAt ℂ
        (⇑((chartAt ℂ x).symm ≫ₕ chartAt ℂ ((chartAt ℂ x).symm w))) w :=
      (hprop.contDiffAt
        (((chartAt ℂ x).symm ≫ₕ chartAt ℂ ((chartAt ℂ x).symm w)).open_source.mem_nhds
          hwτ)).analyticAt
    -- Compose the harmonic reading with the analytic transition.
    have hcomp : HarmonicAt ((u ∘ (chartAt ℂ ((chartAt ℂ x).symm w)).symm) ∘
        ⇑((chartAt ℂ x).symm ≫ₕ chartAt ℂ ((chartAt ℂ x).symm w))) w := by
      refine harmonicAt_comp_analyticAt ?_ hana
      rw [OpenPartialHomeomorph.trans_apply]
      exact hMH
    -- The composite agrees with the reading in `x`'s chart near `w`.
    have hev : ((u ∘ (chartAt ℂ ((chartAt ℂ x).symm w)).symm) ∘
        ⇑((chartAt ℂ x).symm ≫ₕ chartAt ℂ ((chartAt ℂ x).symm w))) =ᶠ[𝓝 w]
        (u ∘ (chartAt ℂ x).symm) := by
      have hcont : ContinuousAt (chartAt ℂ x).symm w := (chartAt ℂ x).continuousAt_symm hwt
      have hnb : ∀ᶠ z in 𝓝 w, (chartAt ℂ x).symm z ∈
          (chartAt ℂ ((chartAt ℂ x).symm w)).source :=
        hcont.eventually_mem
          ((chartAt ℂ ((chartAt ℂ x).symm w)).open_source.mem_nhds (mem_chart_source ℂ _))
      filter_upwards [hnb] with z hz
      simp only [Function.comp_apply, OpenPartialHomeomorph.trans_apply]
      rw [(chartAt ℂ ((chartAt ℂ x).symm w)).left_inv hz]
    exact (harmonicAt_congr_nhds hev).1 hcomp
  -- Readings of the `V n` on the ball, with monotonicity, bound, and convergence.
  have hVread : ∀ n, HarmonicOnNhd ((V n) ∘ (chartAt ℂ x).symm) (ball (chartAt ℂ x x) ρ) :=
    fun n w hw => htrans (V n) (hV n) w hw
  have hmono' : ∀ z ∈ ball (chartAt ℂ x x) ρ,
      Monotone (fun n => ((V n) ∘ (chartAt ℂ x).symm) z) :=
    fun z hz => hmono _ (hmem' z hz)
  have htends' : ∀ z ∈ ball (chartAt ℂ x x) ρ,
      Tendsto (fun n => ((V n) ∘ (chartAt ℂ x).symm) z) atTop
        (𝓝 ((Vlim ∘ (chartAt ℂ x).symm) z)) :=
    fun z hz => htends _ (hmem' z hz)
  have hbdd' : ∀ z ∈ ball (chartAt ℂ x x) ρ, ∀ n,
      ((V n) ∘ (chartAt ℂ x).symm) z ≤ (Vlim ∘ (chartAt ℂ x).symm) z :=
    fun z hz n => (hmono' z hz).ge_of_tendsto (htends' z hz) n
  -- Harnack's principle on the ball, then read off at the center.
  have hlim := harmonicOnNhd_of_monotone_tendsto (V := fun n => (V n) ∘ (chartAt ℂ x).symm)
    (Vlim := Vlim ∘ (chartAt ℂ x).symm) hVread hmono' hbdd' htends'
  exact hlim _ (mem_ball_self hρpos)

/-- **Harnack's dichotomy** on a connected surface: a monotone sequence of
globally harmonic functions either tends to infinity everywhere or converges
everywhere to a harmonic function. -/
theorem mharmonic_dichotomy_of_monotone [ConnectedSpace M]
    {V : ℕ → M → ℝ} (hV : ∀ n, MHarmonicOn (V n) Set.univ)
    (hmono : ∀ x, Monotone (fun n => V n x)) :
    (∀ x, Tendsto (fun n => V n x) atTop atTop) ∨
      ∃ Vlim : M → ℝ, MHarmonicOn Vlim Set.univ ∧
        ∀ x, Tendsto (fun n => V n x) atTop (𝓝 (Vlim x)) := by
  classical
  by_cases hex : ∃ x₀ : M, BddAbove (Set.range fun n => V n x₀)
  case neg =>
    left
    intro x
    exact tendsto_atTop_atTop_of_monotone' (hmono x) fun h => hex ⟨x, h⟩
  case pos =>
    right
    -- Local two-sided Harnack comparison around every point, via the chart
    -- readings of the nonnegative harmonic differences `V n - V 0`.
    have key : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, ∀ n : ℕ,
          V n y - V 0 y ≤ 3 * (V n x - V 0 x) ∧
            V n x - V 0 x ≤ 3 * (V n y - V 0 y) := by
      intro x
      set e := chartAt ℂ x
      -- A ball of radius `2 * r` around the chart image inside the chart target.
      obtain ⟨ε, hε, hball⟩ :=
        Metric.isOpen_iff.mp e.open_target (e x) (mem_chart_target ℂ x)
      set r := ε / 4 with hr
      have hr0 : 0 < r := by rw [hr]; linarith
      have h2r : ball (e x) (2 * r) ⊆ e.target :=
        (ball_subset_ball (by rw [hr]; linarith)).trans hball
      -- Every reading `V n ∘ e.symm` is harmonic on the whole chart target:
      -- transport harmonicity through the analytic transition to the chart
      -- preferred at `e.symm w`.
      have hread : ∀ (n : ℕ), ∀ w ∈ e.target, HarmonicAt (V n ∘ ⇑e.symm) w := by
        intro n w hw
        have hyy : e.symm w ∈ (chartAt ℂ (e.symm w)).source :=
          mem_chart_source ℂ (e.symm w)
        have htrans : AnalyticAt ℂ (⇑(chartAt ℂ (e.symm w)) ∘ ⇑e.symm) w := by
          have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑e.symm) w :=
            contMDiffAt_symm_of_mem_maximalAtlas
              (IsManifold.chart_mem_maximalAtlas x) hw
          have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ (e.symm w))) (e.symm w) :=
            contMDiffAt_of_mem_maximalAtlas
              (IsManifold.chart_mem_maximalAtlas (e.symm w)) hyy
          exact (contMDiffAt_iff_contDiffAt.mp (h2.comp w h1)).analyticAt
        have hmh : HarmonicAt (V n ∘ ⇑(chartAt ℂ (e.symm w)).symm)
            ((⇑(chartAt ℂ (e.symm w)) ∘ ⇑e.symm) w) :=
          hV n (e.symm w) (Set.mem_univ _)
        have hcomp := harmonicAt_comp_analyticAt hmh htrans
        have hev : (V n ∘ ⇑(chartAt ℂ (e.symm w)).symm) ∘
            (⇑(chartAt ℂ (e.symm w)) ∘ ⇑e.symm) =ᶠ[𝓝 w] V n ∘ ⇑e.symm := by
          have hS : IsOpen (e.target ∩ ⇑e.symm ⁻¹' (chartAt ℂ (e.symm w)).source) :=
            e.continuousOn_symm.isOpen_inter_preimage e.open_target
              (chartAt ℂ (e.symm w)).open_source
          filter_upwards [hS.mem_nhds ⟨hw, hyy⟩] with z hz
          simp only [Function.comp_apply]
          rw [(chartAt ℂ (e.symm w)).left_inv hz.2]
        exact (harmonicAt_congr_nhds hev).mp hcomp
      -- The differences read in the chart are nonnegative and harmonic there.
      have hdiff : ∀ n : ℕ,
          HarmonicOnNhd ((V n ∘ ⇑e.symm) - (V 0 ∘ ⇑e.symm)) (ball (e x) (2 * r)) :=
        fun n z hz => (hread n z (h2r hz)).sub (hread 0 z (h2r hz))
      have hpos : ∀ n : ℕ, ∀ z ∈ ball (e x) (2 * r),
          0 ≤ ((V n ∘ ⇑e.symm) - (V 0 ∘ ⇑e.symm)) z := by
        intro n z _
        simp only [Pi.sub_apply, Function.comp_apply, sub_nonneg]
        exact hmono (e.symm z) (Nat.zero_le n)
      have hcx : e.symm (e x) = x := e.left_inv (mem_chart_source ℂ x)
      refine ⟨e.source ∩ ⇑e ⁻¹' ball (e x) r,
        e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball,
        ⟨mem_chart_source ℂ x, mem_ball_self hr0⟩, ?_⟩
      intro y hy n
      obtain ⟨hlow, hup⟩ :=
        harnack_inequality_ball hr0 (hdiff n) (hpos n) (e y) hy.2
      have hcy : e.symm (e y) = y := e.left_inv hy.1
      simp only [Pi.sub_apply, Function.comp_apply, hcx, hcy] at hlow hup
      exact ⟨hup, by linarith⟩
    -- The set of points with bounded orbit is open.
    have hopen : IsOpen {x : M | BddAbove (Set.range fun n => V n x)} := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      obtain ⟨U, hUopen, hxU, hHar⟩ := key x
      obtain ⟨C, hC⟩ := hx
      have hCx : ∀ n : ℕ, V n x ≤ C := fun n => hC (Set.mem_range_self n)
      refine Filter.mem_of_superset (hUopen.mem_nhds hxU) fun y hyU => ?_
      have hyB : BddAbove (Set.range fun n => V n y) := by
        refine ⟨V 0 y + 3 * (C - V 0 x), ?_⟩
        rintro v ⟨n, rfl⟩
        have h1 := (hHar y hyU n).1
        have h2 := hCx n
        change V n y ≤ V 0 y + 3 * (C - V 0 x)
        linarith
      exact hyB
    -- It is also closed: boundedness at one point of the Harnack neighborhood
    -- forces boundedness at the center.
    have hclosed : IsClosed {x : M | BddAbove (Set.range fun n => V n x)} := by
      rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro x hx
      obtain ⟨U, hUopen, hxU, hHar⟩ := key x
      refine Filter.mem_of_superset (hUopen.mem_nhds hxU) fun y hyU => ?_
      intro hyB
      apply hx
      obtain ⟨C, hC⟩ := hyB
      have hCy : ∀ n : ℕ, V n y ≤ C := fun n => hC (Set.mem_range_self n)
      have hxB : BddAbove (Set.range fun n => V n x) := by
        refine ⟨V 0 x + 3 * (C - V 0 y), ?_⟩
        rintro v ⟨n, rfl⟩
        have h2 := (hHar y hyU n).2
        have h3 := hCy n
        change V n x ≤ V 0 x + 3 * (C - V 0 y)
        linarith
      exact hxB
    -- Clopen and nonempty on a connected space: bounded everywhere.
    obtain ⟨x₀, hx₀⟩ := hex
    have huniv : {x : M | BddAbove (Set.range fun n => V n x)} = Set.univ :=
      IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨x₀, hx₀⟩
    have hbdd : ∀ x : M, BddAbove (Set.range fun n => V n x) := by
      intro x
      have hx : x ∈ {x : M | BddAbove (Set.range fun n => V n x)} := by
        rw [huniv]; exact Set.mem_univ x
      exact hx
    have htend : ∀ x : M, Tendsto (fun n => V n x) atTop (𝓝 (⨆ n, V n x)) :=
      fun x => tendsto_atTop_ciSup (hmono x) (hbdd x)
    refine ⟨fun x => ⨆ n, V n x, ?_, fun x => htend x⟩
    exact mharmonicOn_of_monotone_tendsto isOpen_univ hV (fun x _ => hmono x)
      (fun x _ => htend x)

end RiemannDynamics
