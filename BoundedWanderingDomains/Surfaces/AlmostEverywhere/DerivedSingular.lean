module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.SurfaceAlmostEverywhere
public import BoundedWanderingDomains.Surfaces.SingularEncounters.PointConsequences

@[expose] public section

/-! # Almost-everywhere derived-singular accumulation as a consequence of singular encounters -/

open Set Function Filter MeasureTheory OnePoint
open scoped Topology Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

variable [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [ConnectedSpace X] [IsManifold 𝓘(ℂ) 1 X] [MeasurableSpace X] [BorelSpace X]

theorem ae_has_escaping_or_derived_singular_subsequence
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A) :
    ChartAlmostEverywhere A f.HasEscapingOrDerivedSingularSubsequence :=
  (f.ae_has_escaping_or_singular_encounters hf hA hAbad hdis hinj).mono
    (fun _ _ hp => HasEscapingOrSingularEncounters.derived_singular_subsequence f hf hp)

end SurfaceDynamics.LocalMap
