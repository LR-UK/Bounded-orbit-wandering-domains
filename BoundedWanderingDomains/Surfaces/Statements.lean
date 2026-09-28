/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.Surfaces.LocalDynamics
import BoundedWanderingDomains.Surfaces.CompactificationEscape
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.DerivedSet

/-! # Exact surface targets for the paper

These named propositions record the exact surface statements. Their completed
proofs are exported by Solution. This definition layer adds no auxiliary
area estimate, infinite-area limit, or injectivity hypothesis. The independent
Challenge repeats the definitions and all current statements.
-/

open Set Function Filter MeasureTheory OnePoint
open scoped Topology Manifold

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Positive area in some chart; no background metric is chosen. -/
def HasPositiveChartArea (A : Set X) : Prop :=
  ∃ p : X, 0 < volume ((chartAt ℂ p) '' (A ∩ (chartAt ℂ p).source))

namespace LocalMap

def saturation (f : LocalMap X) (A : Set X) : Set X := ⋃ n : ℕ, f.imageAt n A

def InjectiveOnSaturation (f : LocalMap X) (A : Set X) : Prop :=
  InjOn f.map {x : f.source | (x : X) ∈ f.saturation A}

end LocalMap

section Targets
variable [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [ConnectedSpace X] [IsManifold 𝓘(ℂ) 1 X]

/-- Target 2(1): no auxiliary working domain V and no simple connectivity. -/
def NoCompactWanderingOrbitClaim : Prop :=
  ∀ f : LocalMap X, IsOpenHolomorphic f →
    ∀ U : Set X, f.IsWanderingComponent U → ∀ z ∈ U,
      ∀ K : Set X, IsCompact K → K ⊆ f.source →
        ∃ n : ℕ, f.compactifiedIterate n z ∉ ((↑) : X → OnePoint X) '' K

/-- Target 2(2): positive-area wandering sets cannot stay compactly inside O. -/
def NoCompactPositiveAreaWanderingSetClaim [MeasurableSpace X] [BorelSpace X] : Prop :=
  ∀ f : LocalMap X, IsOpenHolomorphic f →
    ∀ A : Set X, MeasurableSet A → A ⊆ f.trapped \ f.omega →
      Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)) →
      f.InjectiveOnSaturation A → HasPositiveChartArea A →
      ¬ ∃ K : Set X, IsCompact K ∧ K ⊆ f.source ∧ f.saturation A ⊆ K

/-- Target 4: compact escape or accumulation at a derived singular value.
The escape alternative has exactly its compact-avoidance meaning by
`tendsto_infty_iff_leaves_compacts`. There is no simple-connectivity or orbit-injectivity hypothesis. -/
def WanderingDerivedSingularLimitClaim : Prop :=
  ∀ f : LocalMap X, IsOpenHolomorphic f →
    ∀ U : Set X, f.IsWanderingComponent U →
      ∀ z ∈ U,
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          (Tendsto (fun k => f.compactifiedIterate (φ k) z) atTop
              (𝓝 (∞ : OnePoint X)) ∨
            ∃ a ∈ derivedSet f.singularValues,
              Tendsto (fun k => f.compactifiedIterate (φ k) z) atTop (𝓝 (a : OnePoint X)))

end Targets
end SurfaceDynamics
