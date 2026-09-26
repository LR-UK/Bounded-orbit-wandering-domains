/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CuspDensityBounds
import BoundedWanderingDomains.Surfaces.FinitePunctureAreaBridge

/-! # Finite intrinsic area near an isolated surface puncture -/

open Set Function Metric MeasureTheory
open scoped Manifold Topology ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]

/-- The inverse image of a small punctured coordinate disc has finite
intrinsic hyperbolic area. -/
theorem hyperbolicArea_cusp_chart_finite (p : DiscCover M)
    {d : OpenPartialHomeomorph M ℂ}
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : ball a R \ {a} ⊆ d.target) :
    p.hyperbolicArea
      (d.symm '' (ball a (R / 2) \ {a})) < ⊤ := by
  let B : Set ℂ := ball a (R / 2) \ {a}
  have hBmeas : MeasurableSet B :=
    measurableSet_ball.diff (measurableSet_singleton a)
  have hBtarget : B ⊆ d.target := by
    intro z hz
    apply hball
    refine ⟨?_, hz.2⟩
    have hzR2 : dist z a < R / 2 := hz.1
    have : R / 2 < R := by linarith
    exact hzR2.trans this
  have hAmeas : MeasurableSet (d.symm '' B) :=
    AreaDeficit.Surfaces.chart_inverse_image_measurable d hBmeas hBtarget
  have hAsource : d.symm '' B ⊆ d.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact d.map_target (hBtarget hz)
  rw [p.hyperbolicArea_apply_chart hd hAmeas hAsource]
  unfold coordinateArea
  have himage : d '' (d.symm '' B) = B := by
    ext z
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      simpa only [d.right_inv (hBtarget hw)] using hw
    · intro hz
      exact ⟨d.symm z, ⟨z, hz, rfl⟩, d.right_inv (hBtarget hz)⟩
  rw [himage]
  exact p.lintegral_chartDensity_sq_cusp_lt_top hd hR hball

end AreaDeficit.Surfaces.DiscCover

#print axioms AreaDeficit.Surfaces.DiscCover.hyperbolicArea_cusp_chart_finite
