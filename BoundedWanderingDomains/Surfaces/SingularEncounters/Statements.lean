module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.EncounterData
public import BoundedWanderingDomains.Surfaces.SingularEncounters.PreimageComponent
public import BoundedWanderingDomains.Surfaces.AlmostEverywhere.Definitions

@[expose] public section

/-! # Public componentwise singular-encounter statements -/

open Set Function Filter Topology OnePoint
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Key definition: singular encounter sequences.
Here f is a continuous local map with open source O in X, W is a
set of starting points, and x is the proposed limiting singular value.
In the wandering-domain application, f is open and holomorphic and
W is a wandering Fatou component.

The claim is that there exist:
* a sequence Q_n of embedded discs containing x and shrinking to x;
* full preimage components U_n of Q_n;
* distinct singular values s_n in Q_n converging to x, each a singular
  value of the restriction f : U_n → Q_n.

There is a strictly increasing sequence φ_n of times such that, for every
compact subset K of W, f^{φ_n}(K) is contained in U_n for all sufficiently
large n. The threshold may depend on K.

In our applications all iterates on W are defined. The successor iterates
f^{φ_n + 1} then converge to x uniformly on each compact subset of W.
Under the open holomorphic hypotheses, the encounter points at times φ_n
leave every compact subset of the source O. For O = ℂ this is convergence
to infinity along these times; in general they may approach the boundary
of O in X. -/
def HasSingularEncounterSequence (f : LocalMap X) (hf : Continuous f.map)
    (W : Set X) (x : X) : Prop :=
  ∃ (Q : ℕ → EmbeddedDisc X) (U : ∀ n, f.PreimageComponent hf (Q n).carrier)
    (φ : ℕ → ℕ) (s : ℕ → X),
    StrictMono φ ∧ Injective s ∧ Tendsto s atTop (𝓝 x) ∧
    (∀ n, s n ∈ f.singularValues) ∧ (∀ n, x ∈ (Q n).carrier) ∧
    (∀ O ∈ 𝓝 x, ∀ᶠ n in atTop, ((Q n).carrier : Set X) ⊆ O) ∧
    (∀ n, s n ∈ (U n).singularValues) ∧
    ∀ K : Set X, IsCompact K → K ⊆ W → ∀ᶠ n in atTop,
      MapsTo (f.totalize^[φ n]) K (U n).carrier

/-- Ambient escape or a componentwise singular-encounter sequence for the point. -/
def HasEscapingOrSingularEncounterSequence (f : LocalMap X) (hf : Continuous f.map)
    (x : X) : Prop :=
  (∃ φ : ℕ → ℕ, StrictMono φ ∧
    Tendsto (fun n => f.compactifiedIterate (φ n) x) atTop (𝓝 (∞ : OnePoint X))) ∨
  ∃ a ∈ derivedSet f.singularValues, f.HasSingularEncounterSequence hf {x} a

end SurfaceDynamics.LocalMap
