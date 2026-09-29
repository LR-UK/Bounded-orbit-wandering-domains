module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.PointEncounterAlternative
public import BoundedWanderingDomains.Surfaces.SingularEncounters.EncounterSourceEscape
public import BoundedWanderingDomains.Surfaces.AlmostEverywhere.Definitions

@[expose] public section

/-! # The earlier orbit alternatives follow from componentwise encounters -/

open Set Function Filter Topology OnePoint
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]

theorem HasEscapingOrSingularEncounters.source_escaping_subsequence
    (f : LocalMap X) (hf : IsOpenHolomorphic f) {x : X}
    (h : f.HasEscapingOrSingularEncounters hf.2.continuous x) :
    f.HasSourceEscapingSubsequence x := by
  classical
  obtain ⟨hx, hesc | ⟨a, henc⟩⟩ := h
  · obtain ⟨φ, hφ, hlim⟩ := hesc
    have hlim' := hlim.congr' (Eventually.of_forall fun n =>
      f.compactifiedIterate_eq_orbit (φ n) ⟨x, hx⟩)
    refine ⟨φ, hφ, ?_⟩
    intro K hK _
    filter_upwards [(tendsto_infty_iff_leaves_compacts _).mp hlim' K hK] with n hn
    rintro ⟨y, hy, he⟩
    rw [f.compactifiedIterate_eq_orbit (φ n) ⟨x, hx⟩] at he
    exact hn (OnePoint.coe_injective he ▸ hy)
  · obtain ⟨φ, hφ, hleave⟩ :=
      HasSingularEncounterSequenceAt.source_escaping_subsequence f hf henc
    refine ⟨φ, hφ, ?_⟩
    intro K hK hKs
    filter_upwards [hleave K hK hKs] with n hn
    rintro ⟨y, hy, he⟩
    rw [f.compactifiedIterate_eq_orbit (φ n) ⟨x, hx⟩] at he
    exact hn (OnePoint.coe_injective he ▸ hy)

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
theorem HasEscapingOrSingularEncounters.derived_singular_subsequence
    (f : LocalMap X) (hf : IsOpenHolomorphic f) {x : X}
    (h : f.HasEscapingOrSingularEncounters hf.2.continuous x) :
    f.HasEscapingOrDerivedSingularSubsequence x := by
  obtain ⟨hx, hesc | ⟨a, henc⟩⟩ := h
  · obtain ⟨φ, hφ, hlim⟩ := hesc
    exact ⟨φ, hφ, Or.inl hlim⟩
  · obtain ⟨φ, hφ, hlim⟩ :=
      HasSingularEncounterSequenceAt.successor_orbit_limit f hf.2.continuous henc (mem_singleton x)
    refine ⟨fun n => φ n + 1, fun _ _ hnm => Nat.add_lt_add_right (hφ hnm) 1,
      Or.inr ⟨a, HasSingularEncounterSequenceAt.derived_mem f hf.2.continuous henc, ?_⟩⟩
    have hh := (OnePoint.continuous_coe.tendsto a).comp hlim
    exact hh.congr' (Eventually.of_forall fun n =>
      (f.compactifiedIterate_eq_orbit (φ n + 1) ⟨x, hx⟩).symm)

end SurfaceDynamics.LocalMap

