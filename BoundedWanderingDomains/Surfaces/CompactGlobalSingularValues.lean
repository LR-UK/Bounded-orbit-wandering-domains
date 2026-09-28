/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactSurfaceCovering
import BoundedWanderingDomains.Surfaces.LocalDynamics
import BoundedWanderingDomains.Surfaces.Statements

open Set Function Topology
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [CompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X]
  [MeasurableSpace X] [BorelSpace X]

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem exists_finite_singularValues_of_compact_global
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (hsource : f.source = ⊤) :
    ∃ B : Finset X, f.singularValues ⊆ B := by
  classical
  have hall : ∀ x : X, x ∈ f.source := by intro x; rw [hsource]; trivial
  let : Nonempty f.source := ⟨⟨Classical.arbitrary X, hall _⟩⟩
  let : CompactSpace f.source := isCompact_iff_compactSpace.mp
    (show IsCompact (f.source : Set X) by simpa only [hsource, TopologicalSpace.Opens.coe_top] using (isCompact_univ : IsCompact (univ : Set X)))
  let : LocallyCompactSpace f.source := f.source.isOpen.locallyCompactSpace
  have hclosed : IsClosed (range f.map) := by
    simpa only [image_univ] using (isCompact_univ.image hf.2.continuous).isClosed
  have hrange : range f.map = univ :=
    (show IsClopen (range f.map) from ⟨hclosed, hf.1.isOpen_range⟩).eq_univ (range_nonempty _)
  obtain ⟨B, hB⟩ := exists_finite_branch_values_isLocalHomeomorphOn hf.2 hf.1
    (isCompact_univ : IsCompact (univ : Set f.source))
  have hcov : IsCoveringMapOn f.map (B : Set X)ᶜ :=
    IsCoveringMapOn.of_isLocalHomeomorphOn hf.2.continuous (hB.mono (fun x hx => ⟨mem_univ _, hx⟩))
  refine ⟨B, ?_⟩
  intro y hy
  by_contra hn
  apply hy
  exact ⟨(B : Set X)ᶜ, B.finite_toSet.isClosed.isOpen_compl, hn,
    (by rw [hrange]; exact subset_univ _), hcov⟩

end SurfaceDynamics.LocalMap
