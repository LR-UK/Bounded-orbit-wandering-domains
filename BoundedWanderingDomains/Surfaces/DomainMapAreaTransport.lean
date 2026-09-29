module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.DomainArea
public import BoundedWanderingDomains.Surfaces.ChartMapAreaTransport

@[expose] public section

/-! # Area transport for hyperbolic subdomain metrics -/

open Set Function MeasureTheory
open scoped Manifold ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ) 1 N] [MeasurableSpace N] [BorelSpace N]
  [SecondCountableTopology N] [T2Space N]

/-- A pointwise pullback identity for subdomain densities transports the
corresponding intrinsic areas on every injective measurable chart patch. -/
theorem chart_domainArea_eq_image_of_pullback_local
    (p : DiscCover M) (q : DiscCover N)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens N)
    {c : OpenPartialHomeomorph M ℂ} {d : OpenPartialHomeomorph N ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {f : M → N}
    {W : Set M} (hW : MeasurableSet W)
    (hWc : W ⊆ c.source) (hfWd : f '' W ⊆ d.source)
    (hfW : MeasurableSet (f '' W)) (hinj : InjOn f W)
    (hder : ∀ z ∈ c '' W,
      HasDerivAt (d ∘ f ∘ c.symm) (deriv (d ∘ f ∘ c.symm) z) z)
    (hpull : ∀ z ∈ c '' W,
      ‖deriv (d ∘ f ∘ c.symm) z‖ *
          q.domainChartDensity V d ((d ∘ f ∘ c.symm) z) =
        p.domainChartDensity U c z) :
    p.domainArea U W = q.domainArea V (f '' W) := by
  let g : ℂ → ℂ := d ∘ f ∘ c.symm
  have hA : MeasurableSet (c '' W) :=
    chart_image_measurable c (p.projection ⟨0, by simp [unitDisc]⟩) hW hWc
  have hginj : InjOn g (c '' W) := by
    rintro z ⟨x, hx, rfl⟩ z' ⟨y, hy, rfl⟩ heq
    have hfx : f x ∈ d.source := hfWd ⟨x, hx, rfl⟩
    have hfy : f y ∈ d.source := hfWd ⟨y, hy, rfl⟩
    have hxy : f x = f y := d.injOn hfx hfy (by
      simpa only [g, comp_apply, c.left_inv (hWc hx), c.left_inv (hWc hy)] using heq)
    exact congrArg c (hinj hx hy hxy)
  have himage : g '' (c '' W) = d '' (f '' W) := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨f x, ⟨x, hx, rfl⟩, by simp [g, c.left_inv (hWc hx)]⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨c x, ⟨x, hx, rfl⟩, by simp [g, c.left_inv (hWc hx)]⟩
  have hgder : ∀ z ∈ c '' W, HasDerivAt g (deriv g z) z := by
    intro z hz
    simpa only [g] using hder z hz
  have hchange := AreaDeficit.holomorphic_change_of_variables hA hgder hginj
    (fun z => ENNReal.ofReal ((q.domainChartDensity V d z)^2))
  rw [p.domainArea_coordinate_formula U hc hW hWc,
    q.domainArea_coordinate_formula V hd hfW hfWd]
  rw [← himage, hchange]
  apply setLIntegral_congr_fun hA
  intro z hz
  change ENNReal.ofReal ((p.domainChartDensity U c z)^2) =
    ENNReal.ofReal (‖deriv g z‖^2) *
      ENNReal.ofReal ((q.domainChartDensity V d (g z))^2)
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  rw [← mul_pow]
  simpa only [g] using (congrArg (fun t : ℝ => t^2) (hpull z hz)).symm

/-- Global holomorphic form of `chart_domainArea_eq_image_of_pullback_local`. -/
theorem chart_domainArea_eq_image_of_pullback
    (p : DiscCover M) (q : DiscCover N)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens N)
    {c : OpenPartialHomeomorph M ℂ} {d : OpenPartialHomeomorph N ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {f : M → N} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    {W : Set M} (hW : MeasurableSet W)
    (hWc : W ⊆ c.source) (hfWd : f '' W ⊆ d.source)
    (hfW : MeasurableSet (f '' W)) (hinj : InjOn f W)
    (hpull : ∀ z ∈ c '' W,
      ‖deriv (d ∘ f ∘ c.symm) z‖ *
          q.domainChartDensity V d ((d ∘ f ∘ c.symm) z) =
        p.domainChartDensity U c z) :
    p.domainArea U W = q.domainArea V (f '' W) := by
  apply p.chart_domainArea_eq_image_of_pullback_local q U V hc hd hW hWc hfWd hfW hinj
  · rintro _ ⟨x, hx, rfl⟩
    simpa only [c.left_inv (hWc hx)] using
      hasDerivAt_writtenInCharts hc hd hf (hWc hx) (hfWd ⟨x, hx, rfl⟩)
  · exact hpull

end AreaDeficit.Surfaces.DiscCover
