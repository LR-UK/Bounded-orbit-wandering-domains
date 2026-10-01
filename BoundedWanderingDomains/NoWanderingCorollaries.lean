module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import Mathlib.Analysis.CStarAlgebra.Classes
public import BoundedWanderingDomains.EntireSurfaceModel
public import BoundedWanderingDomains.Surfaces.FiniteType
public import BoundedWanderingDomains.Surfaces.CompactGlobalSingularValues

@[expose] public section

/-! # Classical no-wandering corollaries

The compact-surface result includes nonconstant rational maps, represented
intrinsically as open holomorphic self-maps of the Riemann sphere. The sphere
statement is valid for every complex atlas, hence for the standard sphere atlas.
The entire and meromorphic statements treat the transcendental case with
finitely many singular values. Polynomial dynamics is included in the compact
sphere case. Every corollary below follows from the general finite-type theorem.
-/

open Set Function Filter OnePoint
open scoped Topology Manifold

namespace BoundedWanderingDomains

/-- A finite-type transcendental entire function has no wandering Fatou domains. -/
theorem no_wandering_domains_transcendental_entire_finite_singularValues
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    (hfinite : (ComplexDynamics.singularValues f).Finite)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (_hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n + 1))) :
    ¬ Pairwise (fun n m : ℕ => Disjoint (U n) (U m)) := by
  intro hdis
  have hnonconst : ¬ ∃ c, ∀ z, f z = c := by
    rintro ⟨c, hc⟩
    exact htrans ⟨Polynomial.C c, fun z => by simpa using hc z⟩
  have hS : (MeromorphicDynamics.surfaceModel f).singularValues.Finite := by
    rw [MeromorphicDynamics.surfaceModel_singularValues]
    exact MeromorphicDynamics.finite_singularValues_of_entire hf hfinite
  exact SurfaceDynamics.no_wandering_domains_finite_type _
    (MeromorphicDynamics.surfaceModel_isOpenHolomorphic_of_entire hf hnonconst) hS _
    (MeromorphicDynamics.surfaceModel_isWanderingComponent_of_fatouComponents
      (fun n => MeromorphicDynamics.isFatouComponent_of_entire hf (hU n)) hforward hdis)

end BoundedWanderingDomains

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [IsManifold 𝓘(ℂ) 1 X]

/-- An open holomorphic self-map of a compact complex one-manifold has no wandering
normality components. In particular this applies to nonconstant rational maps. -/
theorem no_wandering_domains_compact [CompactSpace X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (hglobal : (f.source : Set X) = univ) (U : Set X) :
    ¬ f.IsWanderingComponent U := by
  have hsource : f.source = ⊤ := SetLike.coe_injective hglobal
  obtain ⟨B, hB⟩ := f.exists_finite_singularValues_of_compact_global hf hsource
  exact no_wandering_domains_finite_type f hf (B.finite_toSet.subset hB) U

end SurfaceDynamics

namespace MeromorphicDynamics

/-- The independent challenge's germ-based rationality convention. -/
def IsRationalMeromorphic (f : ℂ → ℂ) : Prop :=
  ∃ p q : Polynomial ℂ, q ≠ 0 ∧
    ∀ a : ℂ, f =ᶠ[𝓝[≠] a] (fun z => p.eval z / q.eval z)

/-- A transcendental meromorphic function with finitely many singular values
on the sphere has no wandering Fatou domains. Poles are included in the
holomorphic source model; the Fatou components avoid poles and prepoles. -/
theorem no_wandering_domains_transcendental_meromorphic_finite_singularValues
    {f : ℂ → ℂ} (hf : MeromorphicNFOn f univ)
    (htrans : ¬ IsRationalMeromorphic f) (hfinite : (singularValues f).Finite)
    {U : ℕ → Set ℂ} (hU : ∀ n, IsFatouComponent f (U n))
    (hforward : ∀ n, MapsTo f (U n) (U (n + 1))) :
    ¬ Pairwise (fun n m : ℕ => Disjoint (U n) (U m)) := by
  intro hdis
  have hS : (surfaceModel f).singularValues.Finite := by
    rwa [surfaceModel_singularValues]
  exact SurfaceDynamics.no_wandering_domains_finite_type (surfaceModel f)
    (surfaceModel_isOpenHolomorphic hf htrans) hS (finiteImage (U 0))
    (surfaceModel_isWanderingComponent_of_fatouComponents hU hforward hdis)

end MeromorphicDynamics

namespace SurfaceDynamics

/-- The rational-map corollary, in the intrinsic holomorphic-sphere formulation.
The source is the whole sphere, so poles and infinity are included. -/
theorem no_wandering_domains_rational
    [T2Space (OnePoint ℂ)] [LocallyCompactSpace (OnePoint ℂ)]
    [ChartedSpace ℂ (OnePoint ℂ)] [IsManifold 𝓘(ℂ) 1 (OnePoint ℂ)]
    (f : LocalMap (OnePoint ℂ)) (hf : IsOpenHolomorphic f)
    (hglobal : (f.source : Set (OnePoint ℂ)) = univ) (U : Set (OnePoint ℂ)) :
    ¬ f.IsWanderingComponent U :=
  no_wandering_domains_compact f hf hglobal U

end SurfaceDynamics
