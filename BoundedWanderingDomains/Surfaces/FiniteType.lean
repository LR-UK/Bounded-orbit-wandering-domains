module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import Mathlib.Analysis.CStarAlgebra.Classes
public import BoundedWanderingDomains.Surfaces.SurfaceDerivedLimits

@[expose] public section

/-! # No wandering domains for finite-type local maps

The target complex one-manifold is compact and may be disconnected; the source can be any open subset. The
derived-singular theorem rules out wandering because a finite singular set
has no derived points and an orbit in a compact target cannot escape.
This includes Epstein's finite-type maps and permits removable punctures.
-/

open Set Function Filter OnePoint
open scoped Topology Manifold

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X]

/-- An open holomorphic map from an arbitrary open subset of a compact
complex one-manifold, possibly disconnected, with finitely many singular values, has no wandering
normality components. No maximality or simple-connectivity assumption on
the source is needed. -/
theorem no_wandering_domains_finite_type
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (hfinite : f.singularValues.Finite) (U : Set X) :
    ¬ f.IsWanderingComponent U := by
  intro hU
  have hwand := hU
  obtain ⟨V, hV0, hVcomp, _, _⟩ := hU
  obtain ⟨z, hz, hVz⟩ := hVcomp 0
  have hzU : z ∈ U := by
    rw [← hV0, hVz]
    exact mem_connectedComponentIn hz
  have hzT := hwand.subset_trapped f hzU
  obtain ⟨φ, _, hescape | ⟨a, ha, _⟩⟩ :=
    wanderingDerivedSingularLimitClaim f hf U hwand z hzU
  · apply not_tendsto_infty_of_range_subset_compact
      (fun n => f.orbit (φ n) ⟨z, hzT⟩) isCompact_univ (fun _ => mem_univ _)
    simpa only [f.compactifiedIterate_eq_orbit _ ⟨z, hzT⟩] using hescape
  · have hac : a ∈ closure (f.singularValues \ {a}) :=
      mem_closure_iff_clusterPt.mpr (accPt_principal_iff_clusterPt.mp ha)
    exact (hfinite.sdiff.isClosed.closure_subset hac).2 (mem_singleton a)

end SurfaceDynamics
