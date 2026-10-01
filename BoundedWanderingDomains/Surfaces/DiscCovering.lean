module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.DiscCover

@[expose] public section

/-! # Disc coverings whose image can be one ambient component

Unlike `DiscCover`, this interface allows empty fibres in other ambient
components. It is used for lifting the local filling argument; metric and
area constructions continue to use the surjective covers of each component.
-/

open scoped Manifold

namespace AreaDeficit.Surfaces

structure DiscCovering (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] where
  projection : unitDisc → X
  holomorphic : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) projection
  covering : IsCoveringMap projection

def DiscCover.toDiscCovering {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] (p : DiscCover X) : DiscCovering X :=
  ⟨p.projection, p.holomorphic, p.covering⟩

instance {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] :
    Coe (DiscCover X) (DiscCovering X) := ⟨DiscCover.toDiscCovering⟩

end AreaDeficit.Surfaces
