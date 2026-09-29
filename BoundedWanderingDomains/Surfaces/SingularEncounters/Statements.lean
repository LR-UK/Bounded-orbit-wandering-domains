module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.EncounterData
public import BoundedWanderingDomains.Surfaces.AlmostEverywhere.Definitions

@[expose] public section

/-! # Public componentwise singular-encounter statements -/

open Set Function Filter Topology OnePoint
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Distinct singular values converge to x through shrinking analytic discs.
The selected full inverse components capture every compact subset of W at
common increasing times. The base points c merely name the components. -/
def HasSingularEncounterSequence (f : LocalMap X) (hf : Continuous f.map)
    (W : Set X) (x : X) : Prop :=
  ∃ (Q : ℕ → EmbeddedDisc X) (φ : ℕ → ℕ) (s : ℕ → X) (c : ℕ → f.source),
    StrictMono φ ∧ Injective s ∧ Tendsto s atTop (𝓝 x) ∧
    (∀ n, s n ∈ f.singularValues) ∧ (∀ n, x ∈ (Q n).carrier) ∧
    (∀ O ∈ 𝓝 x, ∀ᶠ n in atTop, ((Q n).carrier : Set X) ⊆ O) ∧
    (∀ n, s n ∈ f.componentSingularValues hf (Q n).carrier (c n)) ∧
    ∀ L : Set X, IsCompact L → L ⊆ W → ∀ᶠ n in atTop,
      MapsTo (f.totalize^[φ n]) L (f.inverseComponentSource hf (Q n).carrier (c n))

/-- Ambient escape or a componentwise singular-encounter sequence for the point. -/
def HasEscapingOrSingularEncounterSequence (f : LocalMap X) (hf : Continuous f.map)
    (x : X) : Prop :=
  (∃ φ : ℕ → ℕ, StrictMono φ ∧
    Tendsto (fun n => f.compactifiedIterate (φ n) x) atTop (𝓝 (∞ : OnePoint X))) ∨
  ∃ a ∈ derivedSet f.singularValues, f.HasSingularEncounterSequence hf {x} a

end SurfaceDynamics.LocalMap
