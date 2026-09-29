module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.EncounterData
public import BoundedWanderingDomains.Surfaces.CompactificationEscape

@[expose] public section

/-! # The pointwise combined alternative for the measure theorem -/

open Set Function Filter Topology OnePoint

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

def HasEscapingOrSingularEncounters (f : LocalMap X) (hf : Continuous f.map) (x : X) : Prop :=
  ∃ hx : x ∈ f.trapped,
    (∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => f.compactifiedIterate (φ n) x) atTop (𝓝 (∞ : OnePoint X))) ∨
    ∃ a : X, f.HasSingularEncounterSequenceAt hf {x} ⟨x, hx⟩ a

end SurfaceDynamics.LocalMap
