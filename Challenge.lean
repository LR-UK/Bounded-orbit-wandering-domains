module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Topology.UniformSpace.OfCompactT2
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.DerivedSet
public import Mathlib.Geometry.Manifold.Complex
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Analysis.Meromorphic.NormalForm

@[expose] public section

/-! # Independent challenge for wandering-domain and wandering-set results

Nineteen targets cover entire and meromorphic escape, local compact-orbit and
derived-singular accumulation, positive-area and almost-everywhere wandering
sets, the unchanged original entire theorem, and classical no-wandering
corollaries. Descriptive names do not depend on manuscript numbering.

Only Mathlib is imported. These independent proof placeholders are specifications;
the solution supplies proofs without importing this module. The compact-source
and ambient derived-singular formulations are distinguished explicitly.
See docs/PAPER_STATEMENT_ALIGNMENT.md for their mathematical scope.
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

end LocalMap

section Targets
variable [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [ConnectedSpace X] [IsManifold 𝓘(ℂ) 1 X]

/-- Compact-orbit exclusion: no auxiliary working domain V and no simple connectivity. -/
def NoCompactWanderingOrbitClaim : Prop :=
  ∀ f : LocalMap X, IsOpenHolomorphic f →
    ∀ U : Set X, f.IsWanderingComponent U → ∀ z ∈ U,
      ∀ K : Set X, IsCompact K → K ⊆ f.source →
        ∃ n : ℕ, f.compactifiedIterate n z ∉ ((↑) : X → OnePoint X) '' K

/-- Positive-area wandering sets: positive-area wandering sets cannot stay compactly inside O. -/
def NoCompactPositiveAreaWanderingSetClaim [MeasurableSpace X] [BorelSpace X] : Prop :=
  ∀ f : LocalMap X, IsOpenHolomorphic f →
    ∀ A : Set X, MeasurableSet A → A ⊆ f.trapped \ f.omega →
      Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)) →
      f.InjectiveOnSaturation A → HasPositiveChartArea A →
      ¬ ∃ K : Set X, IsCompact K ∧ K ⊆ f.source ∧ f.saturation A ⊆ K

/-- Derived-singular accumulation: compact escape or accumulation at a derived singular value.
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

/-- Meromorphic wandering-domain escape. No simple-connectivity
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

These declarations belong to the independent Palomar-facing statement layer.
Their proofs are intentionally omitted in the challenge file.  A completed
solution must prove these exact propositions without importing this module. -/

namespace BoundedWanderingDomains

theorem wandering_domain_has_locally_uniform_escaping_subsequence : wandering_orbit_locallyUniform_inftyClaim := by
  sorry

theorem wandering_orbit_accumulates_on_derived_singular_values :
    wandering_orbit_pointwise_spherical_singular_derivedSetClaim := by
  sorry

end BoundedWanderingDomains

namespace MeromorphicDynamics

theorem wandering_domain_has_locally_uniform_escaping_subsequence : WanderingLocallyUniformInfinityClaim := by
  sorry

end MeromorphicDynamics

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [ConnectedSpace X] [IsManifold 𝓘(ℂ) 1 X]

theorem wandering_component_orbit_not_compactly_contained : NoCompactWanderingOrbitClaim (X := X) := by
  sorry

theorem positive_area_wandering_saturation_not_compactly_contained [MeasurableSpace X] [BorelSpace X] :
    NoCompactPositiveAreaWanderingSetClaim (X := X) := by
  sorry

theorem wandering_orbit_has_escaping_or_derived_singular_subsequence : WanderingDerivedSingularLimitClaim (X := X) := by
  sorry

end SurfaceDynamics

/-! ## Original entire-function statement (unchanged)

Retained verbatim from the preceding challenge, with the same declaration name
and hypotheses. The revised-paper statements above remain separate targets. -/

namespace BoundedWanderingDomains

theorem no_bounded_wandering_domains_transcendental_entire
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hbounded : Bornology.IsBounded (Set.range (fun n : ℕ => (f^[n]) z))) :
    ¬ Pairwise (fun n m : ℕ => Disjoint (U n) (U m)) := by
  sorry

end BoundedWanderingDomains

/-! ## Classical no-wandering corollaries

The rational statement uses the intrinsic holomorphic-sphere formulation.
The finite-singular-value entire statement explicitly treats the transcendental
case; polynomials are included among rational maps. All classical corollaries
follow from the finite-type theorem below, which also covers meromorphic maps. -/

namespace BoundedWanderingDomains

/-- A finite-type transcendental entire function has no wandering Fatou domains. -/
theorem no_wandering_domains_transcendental_entire_finite_singularValues
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    (hfinite : (ComplexDynamics.singularValues f).Finite)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n + 1))) :
    ¬ Pairwise (fun n m : ℕ => Disjoint (U n) (U m)) := by
  sorry

end BoundedWanderingDomains

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [ConnectedSpace X] [IsManifold 𝓘(ℂ) 1 X]

/-- An open holomorphic self-map of a compact Riemann surface has no wandering
normality components. In particular this applies to nonconstant rational maps. -/
theorem no_wandering_domains_compact [CompactSpace X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (hglobal : (f.source : Set X) = univ) (U : Set X) :
    ¬ f.IsWanderingComponent U := by
  sorry

end SurfaceDynamics

namespace SurfaceDynamics

/-- The rational-map corollary, in the intrinsic holomorphic-sphere formulation.
The source is the whole sphere, so poles and infinity are included. -/
theorem no_wandering_domains_rational
    [T2Space (OnePoint ℂ)] [LocallyCompactSpace (OnePoint ℂ)]
    [ChartedSpace ℂ (OnePoint ℂ)] [IsManifold 𝓘(ℂ) 1 (OnePoint ℂ)]
    (f : LocalMap (OnePoint ℂ)) (hf : IsOpenHolomorphic f)
    (hglobal : (f.source : Set (OnePoint ℂ)) = univ) (U : Set (OnePoint ℂ)) :
    ¬ f.IsWanderingComponent U := by
  sorry

end SurfaceDynamics

/-! ## Compact and almost-everywhere refinements -/

-- Match the canonical complex instances used by the independent definition module.
attribute [-instance] instCommCStarAlgebraComplex

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

attribute [instance] instCommCStarAlgebraComplex

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [ConnectedSpace X] [IsManifold 𝓘(ℂ) 1 X]

theorem compact_wandering_orbit_accumulates_on_derived_singular_values
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {U : Set X} (hU : f.IsWanderingComponent U) {z : X} (hz : z ∈ U)
    {K : Set X} (hK : IsCompact K)
    (horbit : ∀ n, f.compactifiedIterate n z ∈ ((↑) : X → OnePoint X) '' K) :
    ∃ a ∈ K ∩ derivedSet f.singularValues, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => f.compactifiedIterate (φ n) z) atTop (𝓝 (a : OnePoint X)) := by
  sorry

variable [MeasurableSpace X] [BorelSpace X]

theorem almost_every_wandering_point_has_source_escaping_subsequence
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : ∀ n, InjOn (f.compactifiedIterate n) A) :
    ChartAlmostEverywhere A f.HasSourceEscapingSubsequence := by
  sorry

theorem positive_area_wandering_saturation_not_compactly_contained_away_from_derived
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : ∀ n, InjOn (f.compactifiedIterate n) A) (hpos : HasPositiveChartArea A) :
    ¬ ∃ K : Set X, IsCompact K ∧ Disjoint K (derivedSet f.singularValues) ∧ f.saturation A ⊆ K := by
  sorry

theorem almost_every_wandering_point_has_escaping_or_derived_singular_subsequence
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : ∀ n, InjOn (f.compactifiedIterate n) A) :
    ChartAlmostEverywhere A f.HasEscapingOrDerivedSingularSubsequence := by
  sorry

end SurfaceDynamics

/-! ## Finite-type maps and the meromorphic class S corollary

The target surface is compact; its open source need not be compact or maximal.
In particular no exclusion of removable source punctures is assumed.
-/

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [ConnectedSpace X] [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X]

/-- An open holomorphic map on an open subset of a compact Riemann surface
with a finite singular set has no wandering normality components. -/
theorem no_wandering_domains_finite_type
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (hfinite : f.singularValues.Finite) (U : Set X) :
    ¬ f.IsWanderingComponent U := by
  sorry

end SurfaceDynamics

-- Match the canonical complex instances of the sphere-value definition.
attribute [-instance] instCommCStarAlgebraComplex

namespace FunctionTheory

-- The original definition predates the inner-product-space imports here.
attribute [local instance 2000] NormedField.toNormedSpace

/-- The genuine sphere value of a normal meromorphic representative. -/
noncomputable def meromorphicSphereValue (f : ℂ → ℂ) (z : ℂ) : OnePoint ℂ := by
  classical
  exact if AnalyticAt ℂ f z then (f z : OnePoint ℂ) else ∞

end FunctionTheory

namespace MeromorphicDynamics

/-- Values with a neighbourhood covered surjectively by the honest
sphere-valued meromorphic map. -/
def regularValues (f : ℂ → ℂ) : Set (OnePoint ℂ) :=
  {y | ∃ W : Set (OnePoint ℂ), IsOpen W ∧ y ∈ W ∧
    W ⊆ range (FunctionTheory.meromorphicSphereValue f) ∧
    IsCoveringMapOn (FunctionTheory.meromorphicSphereValue f) W}

/-- Singular values on the sphere, including any omitted values. -/
def singularValues (f : ℂ → ℂ) : Set (OnePoint ℂ) := (regularValues f)ᶜ

attribute [instance] instCommCStarAlgebraComplex

/-- A transcendental meromorphic map with a finite singular set on the
sphere has no wandering Fatou domains. -/
theorem no_wandering_domains_transcendental_meromorphic_finite_singularValues
    {f : ℂ → ℂ} (hf : MeromorphicNFOn f univ)
    (htrans : ¬ IsRationalMeromorphic f) (hfinite : (singularValues f).Finite)
    {U : ℕ → Set ℂ} (hU : ∀ n, IsFatouComponent f (U n))
    (hforward : ∀ n, MapsTo f (U n) (U (n + 1))) :
    ¬ Pairwise (fun n m : ℕ => Disjoint (U n) (U m)) := by
  sorry

end MeromorphicDynamics

/-! ## Combined componentwise singular-encounter statements

The definitions below specify full inverse components in the actual source,
genuine singular obstructions of their restrictions, and common visit times.
No injectivity or degree hypothesis is imposed on the wandering-domain map.
-/

attribute [-instance] instCommCStarAlgebraComplex

open Set Function Filter Topology OnePoint
open scoped Manifold

namespace AreaDeficit.Surfaces

def unitDisc : TopologicalSpace.Opens ℂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

end AreaDeficit.Surfaces

open AreaDeficit.Surfaces

namespace SurfaceDynamics

structure EmbeddedDisc (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] where
  param : unitDisc → X
  holomorphic : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) param
  embedding : IsOpenEmbedding param

namespace EmbeddedDisc

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

def carrier (Q : EmbeddedDisc X) : TopologicalSpace.Opens X :=
  ⟨range Q.param, Q.embedding.isOpen_range⟩

end EmbeddedDisc
end SurfaceDynamics

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X]

def restrictSource (f : LocalMap X) (V : TopologicalSpace.Opens X)
    (hV : (V : Set X) ⊆ f.source) : LocalMap X where
  source := V
  map := fun x => f.map ⟨x, hV x.property⟩

noncomputable def totalize (f : LocalMap X) (x : X) : X := by
  classical
  exact if hx : x ∈ f.source then f.map ⟨x, hx⟩ else x


variable [ChartedSpace ℂ X]

def inverseComponentSource (f : LocalMap X) (hf : Continuous f.map)
    (D : TopologicalSpace.Opens X) (a : f.source) : TopologicalSpace.Opens X := by
  let : LocallyConnectedSpace f.source := ChartedSpace.locallyConnectedSpace ℂ f.source
  exact ⟨Subtype.val '' connectedComponentIn (f.map ⁻¹' (D : Set X)) a,
    f.source.isOpen.isOpenMap_subtype_val _ ((D.isOpen.preimage hf).connectedComponentIn)⟩

theorem inverseComponentSource_subset (f : LocalMap X) (hf : Continuous f.map)
    (D : TopologicalSpace.Opens X) (a : f.source) :
    (f.inverseComponentSource hf D a : Set X) ⊆ f.source := by
  rintro x ⟨w, _, rfl⟩
  exact w.2

/-- The restriction to a full inverse component. Its target remains X. -/
def inverseComponentMap (f : LocalMap X) (hf : Continuous f.map)
    (D : TopologicalSpace.Opens X) (a : f.source) : LocalMap X :=
  f.restrictSource (f.inverseComponentSource hf D a) (f.inverseComponentSource_subset hf D a)

/-- Singular obstructions which are approached by image values of this
component. Merely omitted open regions are excluded. -/
def componentSingularValues (f : LocalMap X) (hf : Continuous f.map)
    (D : TopologicalSpace.Opens X) (a : f.source) : Set X :=
  (f.inverseComponentMap hf D a).singularValues ∩
    closure (range (f.inverseComponentMap hf D a).map) ∩ (D : Set X)

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

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [T2Space X] [IsManifold 𝓘(ℂ) 1 X]
  [LocallyCompactSpace X] [SecondCountableTopology X] [ConnectedSpace X]

/-- Unless there is ambient escape, all points of a wandering domain visit
full inverse components carrying distinct singular values in shrinking discs.
The visits are uniform on each compact subset of the initial domain. -/
theorem wandering_domain_has_escaping_or_singular_encounter_sequence
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {U : Set X} (hU : f.IsWanderingComponent U) {z : X} (hz : z ∈ U) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => f.compactifiedIterate (φ n) z) atTop (𝓝 (∞ : OnePoint X))) ∨
    ∃ a ∈ derivedSet f.singularValues, f.HasSingularEncounterSequence hf.2.continuous U a := by
  sorry

variable [MeasurableSpace X] [BorelSpace X]

/-- The same componentwise alternative holds almost everywhere in any
measurable wandering set outside normality whose iterates are injective. -/
theorem almost_every_wandering_point_has_escaping_or_singular_encounter_sequence
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : ∀ n, InjOn (f.compactifiedIterate n) A) :
    ChartAlmostEverywhere A (f.HasEscapingOrSingularEncounterSequence hf.2.continuous) := by
  sorry

end SurfaceDynamics

attribute [instance] instCommCStarAlgebraComplex

namespace MeromorphicDynamics

/-- Every meromorphic wandering orbit accumulates on the spherical derived
singular set. The compact sphere target rules out ambient escape. -/
theorem wandering_orbit_accumulates_on_derived_singular_values
    {f : ℂ → ℂ} (hf : MeromorphicNFOn f univ) (htrans : ¬ IsRationalMeromorphic f)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, IsFatouComponent f (U n)) (hz : z ∈ U 0)
    (hforward : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hdis : Pairwise (fun n m : ℕ => Disjoint (U n) (U m))) :
    ∃ a ∈ derivedSet (singularValues f), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => (((f^[φ n]) z : ℂ) : OnePoint ℂ)) atTop (𝓝 a) := by
  sorry

end MeromorphicDynamics

