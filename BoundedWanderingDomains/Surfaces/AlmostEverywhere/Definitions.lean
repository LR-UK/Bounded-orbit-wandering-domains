/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.Statements

open Set Function Filter MeasureTheory OnePoint
open scoped Topology Manifold

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- A property holds outside a set of area zero in every chart. -/
def ChartAlmostEverywhere (A : Set X) (P : X → Prop) : Prop :=
  ∀ p : X, volume ((chartAt ℂ p) '' ({x ∈ A | ¬ P x} ∩ (chartAt ℂ p).source)) = 0

/-- One subsequence eventually leaves every compact subset of the source. -/
def LocalMap.HasSourceEscapingSubsequence (f : LocalMap X) (x : X) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∀ K : Set X, IsCompact K → K ⊆ f.source →
      ∀ᶠ n in atTop, f.compactifiedIterate (φ n) x ∉ ((↑) : X → OnePoint X) '' K

end SurfaceDynamics

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X]

/-- A subsequence escapes the ambient surface or converges to a derived singular value. -/
def LocalMap.HasEscapingOrDerivedSingularSubsequence (f : LocalMap X) (x : X) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧
    (Tendsto (fun n => f.compactifiedIterate (φ n) x) atTop (𝓝 (∞ : OnePoint X)) ∨
      ∃ a ∈ derivedSet f.singularValues,
        Tendsto (fun n => f.compactifiedIterate (φ n) x) atTop (𝓝 (a : OnePoint X)))

end SurfaceDynamics
