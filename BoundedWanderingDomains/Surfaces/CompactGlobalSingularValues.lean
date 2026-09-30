module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.CompactSurfaceCovering
public import BoundedWanderingDomains.Surfaces.LocalDynamics
public import BoundedWanderingDomains.Surfaces.Statements

@[expose] public section

open Set Function Topology
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [CompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X]
  [MeasurableSpace X] [BorelSpace X]

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] in
theorem exists_finite_singularValues_of_compact_global
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (hsource : f.source = ⊤) :
    ∃ B : Finset X, f.singularValues ⊆ B := by
  classical
  let : CompactSpace f.source := isCompact_iff_compactSpace.mp
    (show IsCompact (f.source : Set X) by simpa only [hsource, TopologicalSpace.Opens.coe_top] using (isCompact_univ : IsCompact (univ : Set X)))
  let : LocallyCompactSpace f.source := f.source.isOpen.locallyCompactSpace
  obtain ⟨B, hB⟩ := exists_finite_branch_values_isLocalHomeomorphOn hf.2 hf.1
    (isCompact_univ : IsCompact (univ : Set f.source))
  have hcov : IsCoveringMapOn f.map (B : Set X)ᶜ :=
    IsCoveringMapOn.of_isLocalHomeomorphOn hf.2.continuous (hB.mono (fun x hx => ⟨mem_univ _, hx⟩))
  refine ⟨B, ?_⟩
  intro y hy
  by_contra hn
  apply hy
  exact ⟨(B : Set X)ᶜ, B.finite_toSet.isClosed.isOpen_compl, hn, hcov⟩

end SurfaceDynamics.LocalMap
