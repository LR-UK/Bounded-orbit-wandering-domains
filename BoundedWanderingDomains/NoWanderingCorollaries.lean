/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.GlobalLimitStatements
import BoundedWanderingDomains.Surfaces.SurfaceOrbitEscape

/-! # Classical no-wandering corollaries

The compact-surface result includes nonconstant rational maps, represented
intrinsically as open holomorphic self-maps of the Riemann sphere. The sphere
statement is valid for every complex atlas, hence for the standard sphere atlas.
The entire statement treats the transcendental case with finitely many finite
singular values. Polynomial dynamics is included in the compact sphere case.
-/

open Set Function Filter OnePoint
open scoped Topology Manifold

namespace BoundedWanderingDomains

/-- A finite-type transcendental entire function has no wandering Fatou domains. -/
theorem no_wandering_domains_transcendental_entire_finite_singularValues
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    (hfinite : (ComplexDynamics.singularValues f).Finite)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n + 1))) :
    ¬ Pairwise (fun n m : ℕ => Disjoint (U n) (U m)) := by
  intro hdis
  obtain ⟨a, ha, _⟩ := wandering_orbit_pointwise_spherical_singular_derivedSet
    hf htrans hU hz hforward hdis
  have hS : (ComplexDynamics.sphericalSingularValues f).Finite :=
    (hfinite.image ((↑) : ℂ → OnePoint ℂ)).insert ∞
  have hac : a ∈ closure (ComplexDynamics.sphericalSingularValues f \ {a}) :=
    mem_closure_iff_clusterPt.mpr (accPt_principal_iff_clusterPt.mp ha)
  have ham := hS.sdiff.isClosed.closure_subset hac
  exact ham.2 (mem_singleton a)

end BoundedWanderingDomains

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [ConnectedSpace X] [IsManifold 𝓘(ℂ) 1 X]

/-- An open holomorphic self-map of a compact Riemann surface has no wandering
normality components. In particular this applies to nonconstant rational maps. -/
theorem no_wandering_domains_compact [CompactSpace X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (hglobal : (f.source : Set X) = univ) (U : Set X) :
    ¬ f.IsWanderingComponent U := by
  intro hU
  have hW := hU
  obtain ⟨V, hV0, hVcomp, _, _⟩ := hW
  obtain ⟨z, hz, hVz⟩ := hVcomp 0
  have hzU : z ∈ U := by
    rw [← hV0, hVz]
    exact mem_connectedComponentIn hz
  have hzT : z ∈ f.trapped := interior_subset (f.omega_subset_trapped_interior hz)
  obtain ⟨n, hn⟩ := noCompactWanderingOrbitClaim f hf U hU z hzU univ
    isCompact_univ (by rw [hglobal])
  apply hn
  exact ⟨f.orbit n ⟨z, hzT⟩, mem_univ _,
    (f.compactifiedIterate_eq_orbit n ⟨z, hzT⟩).symm⟩

end SurfaceDynamics

namespace SurfaceDynamics

/-- The rational-map corollary, in the intrinsic holomorphic-sphere formulation.
The source is the whole sphere, so poles and infinity are included. -/
theorem no_wandering_domains_rational
    [T2Space (OnePoint ℂ)] [LocallyCompactSpace (OnePoint ℂ)]
    [ChartedSpace ℂ (OnePoint ℂ)] [IsManifold 𝓘(ℂ) 1 (OnePoint ℂ)]
    (f : LocalMap (OnePoint ℂ)) (hf : IsOpenHolomorphic f)
    (hglobal : (f.source : Set (OnePoint ℂ)) = univ) (U : Set (OnePoint ℂ)) :
    ¬ f.IsWanderingComponent U :=
  no_wandering_domains_compact f hf hglobal U

end SurfaceDynamics
