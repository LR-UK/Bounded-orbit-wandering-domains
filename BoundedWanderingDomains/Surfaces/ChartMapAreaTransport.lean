module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.HyperbolicArea
public import BoundedWanderingDomains.Surfaces.CoveringMetricPullback
public import BoundedWanderingDomains.HolomorphicTransport

@[expose] public section

/-! # Area transport for a surface map in one pair of charts -/

open Set Function MeasureTheory
open scoped Manifold ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]
  [TopologicalSpace N] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ) 1 N] [MeasurableSpace N] [BorelSpace N]
  [SecondCountableTopology N]

omit [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [IsManifold 𝓘(ℂ, ℂ) 1 N] [MeasurableSpace N] [BorelSpace N] [SecondCountableTopology N] in
/-- A holomorphic surface map, written in holomorphic source and target
charts, has the expected ordinary complex derivative. -/
theorem hasDerivAt_writtenInCharts
    {c : OpenPartialHomeomorph M ℂ} {d : OpenPartialHomeomorph N ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {f : M → N} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    {x : M} (hxc : x ∈ c.source) (hfd : f x ∈ d.source) :
    HasDerivAt (d ∘ f ∘ c.symm) (deriv (d ∘ f ∘ c.symm) (c x)) (c x) := by
  have hci := (mdifferentiableOn_symm hc _ (c.map_source hxc)).mdifferentiableAt
    (c.open_target.mem_nhds (c.map_source hxc))
  have hfi := (hf (c.symm (c x))).comp (c x) hci
  have hfd' : f (c.symm (c x)) ∈ d.source := by
    rwa [c.left_inv hxc]
  have hdi := (hd _ hfd').mdifferentiableAt (d.open_source.mem_nhds hfd')
  exact (hdi.comp (c x) hfi).differentiableAt.hasDerivAt

/-- The planar Jacobian theorem transports an integrated density deficit to
the corresponding intrinsic surface-area comparison whenever the measured
set and its image lie in one source/target chart pair. -/
theorem chart_area_advance_of_density_deficit
    (p : DiscCover M) (q : DiscCover N)
    {c : OpenPartialHomeomorph M ℂ} {d : OpenPartialHomeomorph N ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {f : M → N} {W : Set M} (hW : MeasurableSet W)
    (hWc : W ⊆ c.source) (hfWd : f '' W ⊆ d.source)
    (hfW : MeasurableSet (f '' W)) (hinj : InjOn f W)
    (hhol : ∀ z ∈ c '' W,
      HasDerivAt (d ∘ f ∘ c.symm) (deriv (d ∘ f ∘ c.symm) z) z)
    {C : ℝ≥0∞}
    (hdef : (∫⁻ z in c '' W,
      ENNReal.ofReal ((p.chartDensity c z)^2) -
      ENNReal.ofReal ((‖deriv (d ∘ f ∘ c.symm) z‖ *
        q.chartDensity d ((d ∘ f ∘ c.symm) z))^2)) ≤ C) :
    p.hyperbolicArea W ≤ q.hyperbolicArea (f '' W) + C := by
  classical
  let g : ℂ → ℂ := d ∘ f ∘ c.symm
  have hA : MeasurableSet (c '' W) :=
    chart_image_measurable c (p.projection ⟨0, by simp [unitDisc]⟩) hW hWc
  have hginj : InjOn g (c '' W) := by
    rintro z ⟨x, hx, rfl⟩ z' ⟨y, hy, rfl⟩ heq
    have hfx : f x ∈ d.source := hfWd ⟨x, hx, rfl⟩
    have hfy : f y ∈ d.source := hfWd ⟨y, hy, rfl⟩
    have hxy : f x = f y := d.injOn hfx hfy (by
      simpa only [g, comp_apply, c.left_inv (hWc hx), c.left_inv (hWc hy)] using heq)
    have : x = y := hinj hx hy hxy
    subst y
    rfl
  have himage : g '' (c '' W) = d '' (f '' W) := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨f x, ⟨x, hx, rfl⟩, by simp [g, c.left_inv (hWc hx)]⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨c x, ⟨x, hx, rfl⟩, by simp [g, c.left_inv (hWc hx)]⟩
  have hgtarget : ∀ z ∈ c '' W, g z ∈ d.target := by
    rintro _ ⟨x, hx, rfl⟩
    simpa only [g, comp_apply, c.left_inv (hWc hx)] using
      d.map_source (hfWd ⟨x, hx, rfl⟩)
  let rho : ℂ → ℝ := d.target.piecewise (q.chartDensity d) (fun _ => 0)
  have hrho : Measurable rho := by
    have hcont : ContinuousOn (q.chartDensity d) d.target :=
      fun z hz => (q.chartDensity_contDiffAt hd hz).continuousAt.continuousWithinAt
    exact hcont.measurable_piecewise continuousOn_const d.open_target.measurableSet
  have hrho_g : ∀ z ∈ c '' W, rho (g z) = q.chartDensity d (g z) := by
    intro z hz
    simp [rho, hgtarget z hz]
  have hdef' : (∫⁻ z in c '' W,
      ENNReal.ofReal ((p.chartDensity c z)^2) -
      ENNReal.ofReal ((‖deriv g z‖ * rho (g z))^2)) ≤ C := by
    calc
      _ = (∫⁻ z in c '' W,
          ENNReal.ofReal ((p.chartDensity c z)^2) -
          ENNReal.ofReal ((‖deriv g z‖ * q.chartDensity d (g z))^2)) := by
        apply setLIntegral_congr_fun hA
        intro z hz
        change ENNReal.ofReal ((p.chartDensity c z)^2) -
          ENNReal.ofReal ((‖deriv g z‖ * rho (g z))^2) =
          ENNReal.ofReal ((p.chartDensity c z)^2) -
          ENNReal.ofReal ((‖deriv g z‖ * q.chartDensity d (g z))^2)
        rw [hrho_g z hz]
      _ ≤ C := by simpa only [g] using hdef
  have hgder : ∀ z ∈ c '' W, HasDerivAt g (deriv g z) z := by
    intro z hz
    simpa only [g] using hhol z hz
  have hplane := AreaDeficit.holomorphic_area_advance_of_density_deficit
    (f := g) (d := fun z => deriv g z) (a := p.chartDensity c)
    (rho := rho) (C := C) hA hgder hginj hrho hdef'
  have hgmeas : MeasurableSet (g '' (c '' W)) :=
    hA.image_of_continuousOn_injOn
      (fun z hz => (hhol z hz).continuousAt.continuousWithinAt) hginj
  rw [p.hyperbolicArea_apply_chart hc hW hWc,
    q.hyperbolicArea_apply_chart hd hfW hfWd]
  unfold coordinateArea
  rw [← himage]
  rw [withDensity_apply _ hA, withDensity_apply _ hgmeas] at hplane
  calc
    (∫⁻ z in c '' W, ENNReal.ofReal ((p.chartDensity c z)^2)) ≤
        (∫⁻ z in g '' (c '' W), ENNReal.ofReal ((rho z)^2)) + C := hplane
    _ = (∫⁻ z in g '' (c '' W),
          ENNReal.ofReal ((q.chartDensity d z)^2)) + C := by
      congr 1
      apply setLIntegral_congr_fun hgmeas
      rintro z ⟨w, hw, rfl⟩
      change ENNReal.ofReal ((rho (g w))^2) =
        ENNReal.ofReal ((q.chartDensity d (g w))^2)
      rw [hrho_g w hw]

/-- Holomorphic form of `chart_area_advance_of_density_deficit`. -/
theorem chart_area_advance_of_density_deficit_holomorphic
    (p : DiscCover M) (q : DiscCover N)
    {c : OpenPartialHomeomorph M ℂ} {d : OpenPartialHomeomorph N ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {f : M → N} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    {W : Set M} (hW : MeasurableSet W)
    (hWc : W ⊆ c.source) (hfWd : f '' W ⊆ d.source)
    (hfW : MeasurableSet (f '' W)) (hinj : InjOn f W)
    {C : ℝ≥0∞}
    (hdef : (∫⁻ z in c '' W,
      ENNReal.ofReal ((p.chartDensity c z)^2) -
      ENNReal.ofReal ((‖deriv (d ∘ f ∘ c.symm) z‖ *
        q.chartDensity d ((d ∘ f ∘ c.symm) z))^2)) ≤ C) :
    p.hyperbolicArea W ≤ q.hyperbolicArea (f '' W) + C := by
  apply p.chart_area_advance_of_density_deficit q hc hd hW hWc hfWd hfW hinj
  · rintro _ ⟨x, hx, rfl⟩
    simpa only [c.left_inv (hWc hx)] using
      hasDerivAt_writtenInCharts hc hd hf (hWc hx) (hfWd ⟨x, hx, rfl⟩)
  · exact hdef

/-- On a charted measurable set where a holomorphic covering is injective,
hyperbolic area cannot decrease. -/
theorem chart_hyperbolicArea_le_image_of_covering
    (p : DiscCover M) (q : DiscCover N)
    {c : OpenPartialHomeomorph M ℂ} {d : OpenPartialHomeomorph N ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {f : M → N} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hcov : IsCoveringMap f) {W : Set M} (hW : MeasurableSet W)
    (hWc : W ⊆ c.source) (hfWd : f '' W ⊆ d.source)
    (hfW : MeasurableSet (f '' W)) (hinj : InjOn f W) :
    p.hyperbolicArea W ≤ q.hyperbolicArea (f '' W) := by
  have hpull : ∀ z ∈ c '' W,
      ‖deriv (d ∘ f ∘ c.symm) z‖ *
          q.chartDensity d ((d ∘ f ∘ c.symm) z) =
        p.chartDensity c z := by
    rintro _ ⟨x, hx, rfl⟩
    have hfd : f x ∈ d.source := hfWd ⟨x, hx, rfl⟩
    have h := p.density_covering_pullback q hf hcov hc hd (hWc hx) hfd
    simpa only [chartDensity, comp_apply, c.left_inv (hWc hx),
      d.left_inv hfd, mul_comm] using h
  have hA : MeasurableSet (c '' W) :=
    chart_image_measurable c (p.projection ⟨0, by simp [unitDisc]⟩) hW hWc
  have hdef0 : (∫⁻ z in c '' W,
      ENNReal.ofReal ((p.chartDensity c z)^2) -
      ENNReal.ofReal ((‖deriv (d ∘ f ∘ c.symm) z‖ *
        q.chartDensity d ((d ∘ f ∘ c.symm) z))^2)) ≤ 0 := by
    have heq : (∫⁻ z in c '' W,
        ENNReal.ofReal ((p.chartDensity c z)^2) -
        ENNReal.ofReal ((‖deriv (d ∘ f ∘ c.symm) z‖ *
          q.chartDensity d ((d ∘ f ∘ c.symm) z))^2)) = 0 := by
      apply setLIntegral_eq_zero hA
      intro z hz
      change ENNReal.ofReal ((p.chartDensity c z)^2) -
        ENNReal.ofReal ((‖deriv (d ∘ f ∘ c.symm) z‖ *
          q.chartDensity d ((d ∘ f ∘ c.symm) z))^2) = 0
      rw [hpull z hz, tsub_self]
    exact heq.le
  simpa only [add_zero] using
    p.chart_area_advance_of_density_deficit_holomorphic q hc hd hf
      hW hWc hfWd hfW hinj hdef0

end AreaDeficit.Surfaces.DiscCover
