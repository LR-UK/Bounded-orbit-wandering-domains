module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.BKL.DerivedLimits

@[expose] public section

/-! # The derived-singular-limit theorem without a simple-connectivity hypothesis -/

open scoped Manifold

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X]

theorem nonEscapingWanderingOrbitClusterMeetsDerivedClaim :
    NonEscapingWanderingOrbitClusterMeetsDerivedClaim (X := X) :=
  nonEscapingWanderingOrbitClusterMeetsDerived_without_simpleConnectivity

theorem wanderingDerivedSingularLimitClaim : WanderingDerivedSingularLimitClaim (X := X) :=
  wanderingDerivedSingularLimit_without_simpleConnectivity

end SurfaceDynamics
