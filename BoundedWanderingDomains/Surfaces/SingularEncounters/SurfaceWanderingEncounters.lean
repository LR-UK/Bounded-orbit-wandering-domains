module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.CompactWanderingReduction
public import BoundedWanderingDomains.Surfaces.NoEscapeCompactRange

@[expose] public section

/-! # The combined wandering-domain theorem on an arbitrary target surface -/

open Set Function Filter Topology OnePoint
open AreaDeficit.Surfaces
open scoped Manifold ContDiff

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]

theorem nonEscapingWanderingOrbitSingularEncounters
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (U : Set X)
    (hU : f.IsWanderingComponent U) (z : X) (hz : z ∈ U)
    (hno : ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => f.compactifiedIterate (φ k) z) atTop (𝓝 (∞ : OnePoint X))) :
    ∃ a ∈ derivedSet f.singularValues,
      f.HasSingularEncounterSequenceAt hf.2.continuous U ⟨z, hU.subset_trapped f hz⟩ a := by
  classical
  let : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  have hztrap := hU.subset_trapped f hz
  let zt : f.trapped := ⟨z, hztrap⟩
  have hcompacteq : ∀ n, f.compactifiedIterate n z = (f.orbit n zt : OnePoint X) :=
    fun n => f.compactifiedIterate_eq_orbit n zt
  obtain ⟨K, hK, hzK⟩ := compact_range_of_no_escaping_subsequence (fun n => f.orbit n zt) (by
    intro hh
    apply hno
    simpa only [hcompacteq] using hh)
  obtain ⟨S, hS0, hScomp, hSimage, hSdis⟩ := hU
  have hzS : ∀ n, f.orbit n zt ∈ S n := fun n =>
    hSimage n ⟨z, hz, f.iterate_eq_some_orbit n zt⟩
  obtain ⟨a, ha, henc⟩ := f.compact_wandering_singular_encounters_disconnected hf
    S hScomp hSdis zt hzS hK hzK
  exact ⟨a, ha, hS0 ▸ henc⟩

theorem wanderingSingularEncounterAlternative
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (U : Set X)
    (hU : f.IsWanderingComponent U) (z : X) (hz : z ∈ U) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => f.compactifiedIterate (φ k) z) atTop (𝓝 (∞ : OnePoint X))) ∨
    ∃ a ∈ derivedSet f.singularValues,
      f.HasSingularEncounterSequenceAt hf.2.continuous U ⟨z, hU.subset_trapped f hz⟩ a := by
  by_cases hescape : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => f.compactifiedIterate (φ k) z) atTop (𝓝 (∞ : OnePoint X))
  · exact Or.inl hescape
  · exact Or.inr (nonEscapingWanderingOrbitSingularEncounters f hf U hU z hz hescape)

end SurfaceDynamics
