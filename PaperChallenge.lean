/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.DerivedSet
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Meromorphic.NormalForm

/-! # Independent challenge for the revised paper's introduction

Six proposition targets: entire and meromorphic escape, the two local surface
conclusions, entire derived-set accumulation, and surface derived-set/escape.
The six theorem declarations at the end are independent statement placeholders.
Their proofs are supplied by PaperSolution, which does not import this module.
Only Mathlib is imported here; the placeholders are confined to this specification.

Matched to no-bounded-WD-2.tex, supplied 25 September 2026. In the positive-area
conclusion K is contained in O, as explicitly confirmed by the author. Both
derived-set conclusions use the subsequence n_k. See PAPER_STATEMENT_ALIGNMENT.md.
-/

open Set Function Filter MeasureTheory OnePoint
open scoped Topology Manifold

attribute [-instance] instCommCStarAlgebraComplex
namespace ComplexDynamics

/-- Every subsequence has a locally uniformly convergent further
subsequence, with a limit defined on the actual source set. -/
def IsNormalSequenceOn {α β : Type*} [TopologicalSpace α] [UniformSpace β]
    (F : ℕ → α → β) (U : Set α) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ →
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ g : U → β,
      TendstoLocallyUniformly (fun n (z : U) => F (φ (ψ n)) z) g atTop

/-- The Riemann sphere as the one-point compactification of ℂ. -/
abbrev RiemannSphere := OnePoint ℂ

/-- Its compact Hausdorff uniformity. -/
noncomputable instance riemannSphereUniformSpace : UniformSpace RiemannSphere :=
  uniformSpaceOfCompactR1

/-- Iterates remain plane maps and are then included in the sphere. -/
def sphericalIterate (f : ℂ → ℂ) (n : ℕ) (z : ℂ) : RiemannSphere :=
  ((f^[n]) z : OnePoint ℂ)

/-- Fatou points have a neighbourhood on which the iterates are normal
as sphere-valued functions. -/
def fatouSet (f : ℂ → ℂ) : Set ℂ :=
  {z | ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ IsNormalSequenceOn (sphericalIterate f) U}

/-- An actual connected component of the Fatou set. -/
def IsFatouComponent (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∃ z ∈ fatouSet f, U = connectedComponentIn (fatouSet f) z

end ComplexDynamics

namespace ComplexDynamics

/-- Values with an open neighbourhood over which the entire map is a covering. -/
def regularValueSet (f : ℂ → ℂ) : Set ℂ :=
  {w | ∃ V : Set ℂ, IsOpen V ∧ w ∈ V ∧ IsCoveringMapOn f V}

/-- The closed set of finite singular values. -/
def singularValues (f : ℂ → ℂ) : Set ℂ := (regularValueSet f)ᶜ

/-- Singular values on the sphere; the function itself is never evaluated at infinity. -/
def sphericalSingularValues (f : ℂ → ℂ) : Set (OnePoint ℂ) :=
  insert ∞ (((↑) : ℂ → OnePoint ℂ) '' singularValues f)

end ComplexDynamics


attribute [instance] instCommCStarAlgebraComplex

namespace BoundedWanderingDomains

def wandering_orbit_locallyUniform_inftyClaim : Prop :=
  ∀ {f : ℂ → ℂ} (_hf : Differentiable ℂ f)
    (_htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {U : ℕ → Set ℂ} {z : ℂ}
    (_hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (_hz : z ∈ U 0) (_hforward : ∀ n, MapsTo f (U n) (U (n+1)))
    (_hdis : Pairwise (fun n m => Disjoint (U n) (U m))),
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ TendstoLocallyUniformlyOn
      (fun k w => ((f^[φ k]) w : OnePoint ℂ))
      (fun _ => (∞ : OnePoint ℂ)) atTop (U 0)

def wandering_orbit_pointwise_spherical_singular_derivedSetClaim : Prop :=
  ∀ {f : ℂ → ℂ} (_hf : Differentiable ℂ f)
    (_htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {U : ℕ → Set ℂ} {z : ℂ}
    (_hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (_hz : z ∈ U 0) (_hforward : ∀ n, MapsTo f (U n) (U (n+1)))
    (_hdis : Pairwise (fun n m => Disjoint (U n) (U m))),
    ∃ a ∈ derivedSet (ComplexDynamics.sphericalSingularValues f), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto
        (fun k => ((f^[φ k]) z : OnePoint ℂ)) atTop (𝓝 a)

end BoundedWanderingDomains

-- Preserve the instance environment of the existing surface definitions.
attribute [-instance] instCommCStarAlgebraComplex

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X]

/-- A local map, with the open source supplied explicitly. -/
structure LocalMap (X : Type*) [TopologicalSpace X] where
  source : TopologicalSpace.Opens X
  map : source → X

namespace LocalMap

/-- One step of local iteration, undefined outside the source. -/
noncomputable def step (f : LocalMap X) (x : X) : Option X := by
  classical
  exact if h : x ∈ f.source then Option.some (f.map ⟨x, h⟩) else Option.none

/-- Partial iterates. No value is assigned to the original map outside its source. -/
noncomputable def iterate (f : LocalMap X) : ℕ → X → Option X
  | 0, x => Option.some x
  | n + 1, x => (f.step x).bind (f.iterate n)

/-- Points whose entire orbit is defined and remains in the source. -/
def trapped (f : LocalMap X) : Set X :=
  {x | ∀ n : ℕ, ∃ y ∈ f.source, f.iterate n x = Option.some y}

/-- The n-th image of a set under partial iteration. -/
def imageAt (f : LocalMap X) (n : ℕ) (A : Set X) : Set X :=
  {y | ∃ x ∈ A, f.iterate n x = Option.some y}

/-- The compactified partial iterate; only its restriction to trapped points
is used to formulate normality. -/
noncomputable def compactifiedIterate (f : LocalMap X) (n : ℕ) (x : X) : OnePoint X :=
  match f.iterate n x with
  | Option.none => OnePoint.infty
  | Option.some y => (y : OnePoint X)

section Normality
variable [T2Space X] [LocallyCompactSpace X]

local instance compactificationUniformSpace : UniformSpace (OnePoint X) :=
  uniformSpaceOfCompactR1

/-- Subsequence normality on the actual source subset. -/
def IsNormalOn (f : LocalMap X) (W : Set X) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ →
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ g : W → OnePoint X,
      TendstoLocallyUniformly
        (fun n (x : W) => f.compactifiedIterate (φ (ψ n)) x) g atTop

/-- The normality locus inside the interior of the trapped set. -/
def omega (f : LocalMap X) : Set X :=
  {x | ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ f.trapped ∧ f.IsNormalOn W}

def IsComponent (f : LocalMap X) (U : Set X) : Prop :=
  ∃ z ∈ f.omega, U = connectedComponentIn f.omega z

/-- Images lie in pairwise distinct components of the normality locus. -/
def IsWanderingComponent (f : LocalMap X) (U : Set X) : Prop :=
  ∃ V : ℕ → Set X, V 0 = U ∧ (∀ n, f.IsComponent (V n)) ∧
    (∀ n, f.imageAt n U ⊆ V n) ∧ Pairwise (fun n m => Disjoint (V n) (V m))

end Normality

/-- Regular values of the local map, with a surjective covering over a neighbourhood.
The extra image condition makes the covering convention explicit. -/
def regularValues (f : LocalMap X) : Set X :=
  {y | ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ W ⊆ range f.map ∧ IsCoveringMapOn f.map W}

def singularValues (f : LocalMap X) : Set X := (f.regularValues)ᶜ


end LocalMap

/-- The hypotheses on the local map in the surface statements. -/
def IsOpenHolomorphic [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) : Prop :=
  IsOpenMap f.map ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map

end SurfaceDynamics

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Positive area in some chart; no background metric is chosen. -/
def HasPositiveChartArea (A : Set X) : Prop :=
  ∃ p : X, 0 < volume ((chartAt ℂ p) '' (A ∩ (chartAt ℂ p).source))

namespace LocalMap

def saturation (f : LocalMap X) (A : Set X) : Set X := ⋃ n : ℕ, f.imageAt n A

def InjectiveOnSaturation (f : LocalMap X) (A : Set X) : Prop :=
  InjOn f.map {x : f.source | (x : X) ∈ f.saturation A}

variable [T2Space X] [LocallyCompactSpace X]

/-- The simply-connected-orbit hypothesis refers to actual normality components. -/
def HasSimplyConnectedComponentOrbit (f : LocalMap X) (U : Set X) : Prop :=
  ∀ n : ℕ, ∀ z ∈ f.imageAt n U,
    SimplyConnectedSpace (connectedComponentIn f.omega z)

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
`tendsto_infty_iff_leaves_compacts`. There is no orbit-injectivity hypothesis. -/
def WanderingDerivedSingularLimitClaim : Prop :=
  ∀ f : LocalMap X, IsOpenHolomorphic f →
    ∀ U : Set X, f.IsWanderingComponent U →
      f.HasSimplyConnectedComponentOrbit U → ∀ z ∈ U,
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          (Tendsto (fun k => f.compactifiedIterate (φ k) z) atTop
              (𝓝 (∞ : OnePoint X)) ∨
            ∃ a ∈ derivedSet f.singularValues,
              Tendsto (fun k => f.compactifiedIterate (φ k) z) atTop (𝓝 (a : OnePoint X)))

end Targets
end SurfaceDynamics

attribute [instance] instCommCStarAlgebraComplex

namespace MeromorphicDynamics

/- A normalized finite representative specifies a meromorphic function:
removable singularities are filled and poles have canonical representative
values. Iteration below is used only on pole-avoiding neighbourhoods, so the
representative's value at a pole is never used in an admissible orbit.
The germ-based rationality convention follows the bundled
FunctionTheory.Meromorphic.RationalInfinity definition. -/

def IsRationalMeromorphic (f : ℂ → ℂ) : Prop :=
  ∃ p q : Polynomial ℂ, q ≠ 0 ∧
    ∀ a : ℂ, f =ᶠ[𝓝[≠] a] (fun z => p.eval z / q.eval z)

-- Match the canonical complex instances used by the meromorphic definitions.
attribute [-instance] instCommCStarAlgebraComplex

/-- Every iterate is a regular finite point of the meromorphic map. -/
def poleAvoidingSet (f : ℂ → ℂ) : Set ℂ :=
  {z | ∀ n : ℕ, AnalyticAt ℂ f ((f^[n]) z)}

/-- Normality on genuine neighbourhoods avoiding all poles and prepoles. -/
def fatouSet (f : ℂ → ℂ) : Set ℂ :=
  {z | ∃ W : Set ℂ, IsOpen W ∧ z ∈ W ∧ W ⊆ poleAvoidingSet f ∧
    ComplexDynamics.IsNormalSequenceOn (ComplexDynamics.sphericalIterate f) W}

def IsFatouComponent (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∃ z ∈ fatouSet f, U = connectedComponentIn (fatouSet f) z

attribute [instance] instCommCStarAlgebraComplex

/-- The meromorphic part of thm:boundedorbitentire. No simple-connectivity
or orbit-injectivity assumption. Convergence is locally uniform and spherical.
MeromorphicNFOn is a representation convention, not an exclusion of poles. -/
def WanderingLocallyUniformInfinityClaim : Prop :=
  ∀ {f : ℂ → ℂ}, MeromorphicNFOn f univ → ¬ IsRationalMeromorphic f →
    ∀ {U : ℕ → Set ℂ} {z : ℂ},
      (∀ n, IsFatouComponent f (U n)) → z ∈ U 0 →
      (∀ n, MapsTo f (U n) (U (n+1))) →
      Pairwise (fun n m => Disjoint (U n) (U m)) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ TendstoLocallyUniformlyOn
        (fun k w => ((f^[φ k]) w : OnePoint ℂ))
        (fun _ => (∞ : OnePoint ℂ)) atTop (U 0)

end MeromorphicDynamics

/-! ## Revised-paper challenge declarations

These six declarations are the independent Palomar-facing statement layer.
Their proofs are intentionally omitted in the challenge file.  A completed
solution must prove these exact propositions without importing this module. -/

namespace BoundedWanderingDomains

theorem theorem_1_2_entire : wandering_orbit_locallyUniform_inftyClaim := by
  sorry

theorem theorem_1_4 :
    wandering_orbit_pointwise_spherical_singular_derivedSetClaim := by
  sorry

end BoundedWanderingDomains

namespace MeromorphicDynamics

theorem theorem_1_2_meromorphic : WanderingLocallyUniformInfinityClaim := by
  sorry

end MeromorphicDynamics

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [ConnectedSpace X] [IsManifold 𝓘(ℂ) 1 X]

theorem theorem_1_3_orbit : NoCompactWanderingOrbitClaim (X := X) := by
  sorry

theorem theorem_1_3_positive_area [MeasurableSpace X] [BorelSpace X] :
    NoCompactPositiveAreaWanderingSetClaim (X := X) := by
  sorry

theorem theorem_1_5 : WanderingDerivedSingularLimitClaim (X := X) := by
  sorry

end SurfaceDynamics
