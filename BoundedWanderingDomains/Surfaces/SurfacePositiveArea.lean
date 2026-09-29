module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.AlmostEverywhere.CompactSource

@[expose] public section

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
  intro f hf A hA hAbad hdis hinj hApos
  rintro ⟨K, hK, hKs, hsatK⟩
  obtain ⟨x, hx, φ, _, hleave⟩ := hApos.exists_of_chartAlmostEverywhere
    (f.ae_has_source_escaping_subsequence hf hA hAbad hdis hinj)
  obtain ⟨n, hn⟩ := (hleave K hK hKs).exists
  let z : f.trapped := ⟨x, (hAbad hx).1⟩
  exact hn ⟨f.orbit (φ n) z,
    hsatK (mem_iUnion.mpr ⟨φ n, x, hx, f.iterate_eq_some_orbit (φ n) z⟩),
    (f.compactifiedIterate_eq_orbit (φ n) z).symm⟩

end SurfaceDynamics
