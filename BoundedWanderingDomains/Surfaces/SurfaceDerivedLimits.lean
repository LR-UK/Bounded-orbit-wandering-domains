module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.SurfaceWanderingEncounters

@[expose] public section

/-! # Derived singular accumulation as a corollary of singular encounters -/

open Set Function Filter Topology OnePoint
open scoped Manifold

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X]

theorem nonEscapingWanderingOrbitClusterMeetsDerivedClaim :
    NonEscapingWanderingOrbitClusterMeetsDerivedClaim (X := X) := by
  intro f hf U hU z hz hno
  obtain ⟨a, ha, henc⟩ := nonEscapingWanderingOrbitSingularEncounters f hf U hU z hz hno
  let zt : f.trapped := ⟨z, hU.subset_trapped f hz⟩
  obtain ⟨φ, hφ, hlim⟩ :=
    LocalMap.HasSingularEncounterSequenceAt.successor_orbit_limit f hf.2.continuous henc hz
  refine ⟨a, ha, fun n => φ n + 1, ?_, ?_⟩
  · intro n m hnm
    exact Nat.add_lt_add_right (hφ hnm) 1
  · apply ((OnePoint.continuous_coe.tendsto a).comp hlim).congr'
    exact Eventually.of_forall (fun n => (f.compactifiedIterate_eq_orbit (φ n + 1) zt).symm)

theorem wanderingDerivedSingularLimitClaim : WanderingDerivedSingularLimitClaim (X := X) :=
  wanderingDerivedSingularLimitClaim_of_nonEscapingClusterMeetsDerived
    nonEscapingWanderingOrbitClusterMeetsDerivedClaim

end SurfaceDynamics
