/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactGlobalPositiveArea
import BoundedWanderingDomains.Surfaces.CompactLocalAreaAdvance

open Set Function MeasureTheory
open scoped Manifold Topology

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- The exact positive-area theorem for every local open holomorphic map on
an arbitrary Riemann surface. -/
theorem noCompactPositiveAreaWanderingSetClaim :
    NoCompactPositiveAreaWanderingSetClaim (X := X) := by
  classical
  intro f hf A hA hAbad hdis hinj hApos
  rintro ⟨K, hK, hKs, hsatK⟩
  by_cases hKuniv : K = univ
  · letI : CompactSpace X := isCompact_univ_iff.mp (hKuniv ▸ hK)
    have hsource : f.source = ⊤ := by
      ext x
      constructor
      · intro _; trivial
      · intro _; exact hKs (hKuniv.symm ▸ mem_univ x)
    exact false_of_compact_global_positive_area_wandering f hf hsource hA hAbad hdis hinj hApos
  · exact noProperCompactPositiveAreaWanderingSet f hf A hA hAbad hdis hinj hApos
      ⟨K, hK, hKuniv, hKs, hsatK⟩

end SurfaceDynamics
