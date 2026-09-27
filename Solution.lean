/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.EntireBoundedOrbit
import BoundedWanderingDomains.GlobalLimitStatements
import BoundedWanderingDomains.MeromorphicEscape
import BoundedWanderingDomains.Surfaces.SurfaceOrbitEscape
import BoundedWanderingDomains.Surfaces.SurfaceDerivedLimits
import BoundedWanderingDomains.Surfaces.SurfacePositiveArea

/-! # Proofs of the revised paper statements

This file is the solution-side entry point for `Challenge.lean`.  Each
declaration repeats its independent challenge type rather than importing the
challenge file. The original entire-function bounded-orbit statement is
exposed unchanged by the shared EntireBoundedOrbit module.
-/

open Set Function Filter OnePoint
open scoped Topology Manifold

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

theorem theorem_1_2_entire : wandering_orbit_locallyUniform_inftyClaim := by
  intro f hf htrans U z hU hz hforward hdis
  exact wandering_orbit_locallyUniform_infty hf htrans hU hz hforward hdis

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

theorem theorem_1_4 : wandering_orbit_pointwise_spherical_singular_derivedSetClaim := by
  intro f hf htrans U z hU hz hforward hdis
  exact wandering_orbit_pointwise_spherical_singular_derivedSet
    hf htrans hU hz hforward hdis

end BoundedWanderingDomains

namespace MeromorphicDynamics

/-- The independent challenge's germ-based rationality convention. -/
def IsRationalMeromorphic (f : ℂ → ℂ) : Prop :=
  ∃ p q : Polynomial ℂ, q ≠ 0 ∧
    ∀ a : ℂ, f =ᶠ[𝓝[≠] a] (fun z => p.eval z / q.eval z)

def WanderingLocallyUniformInfinityClaim : Prop :=
    ∀ {f : ℂ → ℂ}, MeromorphicNFOn f univ →
      ¬ IsRationalMeromorphic f →
      ∀ {U : ℕ → Set ℂ} {z : ℂ},
        (∀ n, IsFatouComponent f (U n)) → z ∈ U 0 →
        (∀ n, MapsTo f (U n) (U (n + 1))) →
        Pairwise (fun n m => Disjoint (U n) (U m)) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ TendstoLocallyUniformlyOn
          (fun k w => ((f^[φ k]) w : OnePoint ℂ))
          (fun _ => (∞ : OnePoint ℂ)) atTop (U 0)

theorem theorem_1_2_meromorphic : WanderingLocallyUniformInfinityClaim :=
  wanderingLocallyUniformInfinityClaim_of_surface_theorem
    SurfaceDynamics.noCompactWanderingOrbitClaim

end MeromorphicDynamics

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [ConnectedSpace X] [IsManifold 𝓘(ℂ) 1 X]

theorem theorem_1_3_orbit : NoCompactWanderingOrbitClaim (X := X) :=
  noCompactWanderingOrbitClaim

theorem theorem_1_5 : WanderingDerivedSingularLimitClaim (X := X) :=
  wanderingDerivedSingularLimitClaim

variable
  [MeasurableSpace X] [BorelSpace X]

theorem theorem_1_3_positive_area : NoCompactPositiveAreaWanderingSetClaim (X := X) :=
  noCompactPositiveAreaWanderingSetClaim

/-- The exact positive-area statement of Theorem 1.3(2) for every
noncompact Riemann surface. -/
theorem theorem_1_3_positive_area_noncompact [NoncompactSpace X] :
    NoCompactPositiveAreaWanderingSetClaim (X := X) := by
  letI : DecidableEq X := Classical.decEq X
  exact noCompactPositiveAreaWanderingSetClaim_of_noncompact

/-- The exact positive-area statement of Theorem 1.3(2) for every
hyperbolic Riemann surface, including compact ones. -/
theorem theorem_1_3_positive_area_hyperbolic
    (hX : RiemannDynamics.IsHyperbolic X) :
    NoCompactPositiveAreaWanderingSetClaim (X := X) := by
  letI : DecidableEq X := Classical.decEq X
  exact noCompactPositiveAreaWanderingSetClaim_of_isHyperbolic hX

end SurfaceDynamics
