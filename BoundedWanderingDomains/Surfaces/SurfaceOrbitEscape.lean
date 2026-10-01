module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.SurfaceWanderingEncounters
public import BoundedWanderingDomains.Surfaces.SingularEncounters.EncounterSourceEscape

@[expose] public section

/-! # Compact source-orbit exclusion as a corollary of singular encounters -/

open Set Function Filter Topology
open scoped Manifold

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]

theorem noCompactWanderingOrbitClaim : NoCompactWanderingOrbitClaim (X := X) := by
  classical
  intro f hf U hU z hz K hK hKs
  by_contra hno
  push Not at hno
  let zt : f.trapped := ⟨z, hU.subset_trapped f hz⟩
  have hzK : ∀ n, f.orbit n zt ∈ K :=
    f.orbit_mem_of_compactifiedIterate_mem_image zt.property hno
  rcases wanderingSingularEncounterAlternative f hf U hU z hz with hescape | ⟨x, _, henc⟩
  · obtain ⟨φ, _, hφ⟩ := hescape
    apply not_tendsto_infty_of_range_subset_compact (fun n => f.orbit (φ n) zt) hK
      (fun n => hzK (φ n))
    exact hφ.congr' (Eventually.of_forall fun n => f.compactifiedIterate_eq_orbit (φ n) zt)
  · obtain ⟨φ, _, hφ⟩ :=
      LocalMap.HasSingularEncounterSequenceAt.source_escaping_subsequence f hf henc
    obtain ⟨n, hn⟩ := (hφ K hK hKs).exists
    exact hn (hzK (φ n))

end SurfaceDynamics
