module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.SurfaceAlmostEverywhere
public import BoundedWanderingDomains.Surfaces.SingularEncounters.PointConsequences

@[expose] public section

/-! # Almost-everywhere source escape as a consequence of singular encounters -/

open Set Function Filter MeasureTheory OnePoint
open scoped Topology Manifold

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Every compact subset of the actual source is left arbitrarily late. -/
def LocalMap.FrequentlyLeavesSourceCompacts (f : LocalMap X) (x : X) : Prop :=
  ∀ K : Set X, IsCompact K → K ⊆ f.source →
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      f.compactifiedIterate n x ∉ ((↑) : X → OnePoint X) '' K

namespace LocalMap

variable [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [ConnectedSpace X] [IsManifold 𝓘(ℂ) 1 X] [MeasurableSpace X] [BorelSpace X]

theorem ae_has_source_escaping_subsequence
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A) :
    ChartAlmostEverywhere A f.HasSourceEscapingSubsequence :=
  (f.ae_has_escaping_or_singular_encounters hf hA hAbad hdis hinj).mono
    (fun _ _ hp => HasEscapingOrSingularEncounters.source_escaping_subsequence f hf hp)

theorem ae_frequently_leaves_source_compacts
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A) :
    ChartAlmostEverywhere A f.FrequentlyLeavesSourceCompacts := by
  apply (f.ae_has_source_escaping_subsequence hf hA hAbad hdis hinj).mono
  intro x _ hx K hK hKs N
  obtain ⟨φ, hφ, hleave⟩ := hx
  obtain ⟨n, hn, hN⟩ := ((hleave K hK hKs).and
    (hφ.tendsto_atTop.eventually_ge_atTop N)).exists
  exact ⟨φ n, hN, hn⟩

end LocalMap
end SurfaceDynamics
