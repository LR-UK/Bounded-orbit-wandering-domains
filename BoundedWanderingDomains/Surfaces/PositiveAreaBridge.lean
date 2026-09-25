/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.AreaNullSets
import BoundedWanderingDomains.Surfaces.Statements

/-! # Positive chart area implies positive intrinsic hyperbolic area

This connects the area condition in the dynamical surface statement with the
intrinsic measure derived from a holomorphic disc covering. -/

open Set MeasureTheory
open scoped Manifold

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

theorem HasPositiveChartArea.hyperbolicArea_pos {A : Set X}
    (hA : HasPositiveChartArea A) (hm : MeasurableSet A)
    (p : AreaDeficit.Surfaces.DiscCover X) :
    0 < p.hyperbolicArea A := by
  obtain ⟨x, hx⟩ := hA
  let c := chartAt ℂ x
  have hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source := by
    intro y hy
    exact (mdifferentiableAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas _) hy).mdifferentiableWithinAt
  have hAc : MeasurableSet (A ∩ c.source) := hm.inter c.open_source.measurableSet
  have hpos : 0 < p.hyperbolicArea (A ∩ c.source) :=
    (p.hyperbolicArea_pos_iff_chart hc hAc inter_subset_right).2 hx
  exact lt_of_lt_of_le hpos (measure_mono inter_subset_left)

end SurfaceDynamics
