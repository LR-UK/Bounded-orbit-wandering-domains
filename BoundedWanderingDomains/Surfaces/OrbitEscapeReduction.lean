module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.WanderingOrbitStructure

@[expose] public section

/-! # Reduction of compact orbit escape to the analytic area core -/

open Set Function
open scoped Topology Manifold

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [ConnectedSpace X] [IsManifold 𝓘(ℂ) 1 X]

/-- The analytic form of the compact-orbit exclusion theorem: pairwise disjoint normality
components cannot contain a marked orbit confined to a compact subset of the
source.  The wrapper theorem below shows that this is exactly the remaining
area contradiction after unpacking `IsWanderingComponent`. -/
def CompactComponentOrbitImpossibleClaim : Prop :=
  ∀ (f : LocalMap X), IsOpenHolomorphic f →
    ∀ (V : ℕ → Set X), (∀ n, f.IsComponent (V n)) →
      Pairwise (fun n m => Disjoint (V n) (V m)) →
      ∀ (z : X) (hz : z ∈ f.trapped),
        (∀ n, f.orbit n ⟨z, hz⟩ ∈ V n) →
        ∀ K : Set X, IsCompact K → K ⊆ f.source →
          (∀ n, f.orbit n ⟨z, hz⟩ ∈ K) → False

omit [SecondCountableTopology X] [ConnectedSpace X] in
theorem noCompactWanderingOrbitClaim_of_componentOrbitImpossible
    (hcore : CompactComponentOrbitImpossibleClaim (X := X)) :
    NoCompactWanderingOrbitClaim (X := X) := by
  intro f hf U hU z hz K hK hKsource
  by_contra hescape
  push Not at hescape
  obtain ⟨V, hztrapped, hV0, hcomp, horbit, hdis⟩ :=
    hU.exists_orbit_components f hz
  apply hcore f hf V hcomp hdis z hztrapped horbit K hK hKsource
  exact f.orbit_mem_of_compactifiedIterate_mem_image hztrapped hescape

end SurfaceDynamics
