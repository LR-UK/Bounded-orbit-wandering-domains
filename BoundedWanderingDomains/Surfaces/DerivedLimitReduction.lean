/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.Statements

/-! # Topological reduction for the derived-singular-limit theorem

The target only needs one suitable subsequence. The analytic obligation is
restricted to orbits without a compact-escaping subsequence; it does not
classify every finite limit or require a finite limit of an escaping orbit. -/

open Set Function Filter OnePoint
open scoped Topology Manifold

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- If all finite subsequential limits lie in `S`, compactness of the
one-point compactification gives the exact escape-or-`S` alternative used in
the paper. -/
theorem escape_or_subsequence_tendsto_mem [FirstCountableTopology X]
    (S : Set X) (u : ℕ → X)
    (hfinite : ∀ (a : X) (φ : ℕ → ℕ), StrictMono φ →
      Tendsto (u ∘ φ) atTop (𝓝 a) → a ∈ S) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (Tendsto (fun k => (u (φ k) : OnePoint X)) atTop
          (𝓝 (∞ : OnePoint X)) ∨
        ∃ a ∈ S, Tendsto (fun k => (u (φ k) : OnePoint X)) atTop
          (𝓝 (a : OnePoint X))) := by
  rcases escape_or_convergent_subsequence u with hesc | ⟨a,φ,hφ,hlim⟩
  · refine ⟨id, strictMono_id, Or.inl ?_⟩
    simpa only [id_eq] using hesc
  · refine ⟨φ,hφ,Or.inr ⟨a,hfinite a φ hφ hlim,?_⟩⟩
    exact (continuous_coe.tendsto a).comp hlim

variable [LocallyCompactSpace X]

/-- Every point of a wandering normality component is trapped, so its partial
iterates are genuine points of the surface. -/
theorem LocalMap.IsWanderingComponent.subset_trapped (f : LocalMap X)
    {U : Set X} (hU : f.IsWanderingComponent U) : U ⊆ f.trapped := by
  rintro z hz
  obtain ⟨V,hV0,hcomp,_,_⟩ := hU
  obtain ⟨w,hw,hVw⟩ := hcomp 0
  apply f.omega_subset_trapped_interior.trans interior_subset
  have hzV : z ∈ V 0 := hV0.symm ▸ hz
  rw [hVw] at hzV
  exact connectedComponentIn_subset f.omega w hzV

section Manifold

variable [ChartedSpace ℂ X] [SecondCountableTopology X] [ConnectedSpace X]
  [IsManifold 𝓘(ℂ) 1 X]

/-- The analytic core left after the compactification argument: every finite
subsequential limit of a simply-connected wandering orbit is a derived
singular value. -/
def FiniteWanderingOrbitLimitsDerivedClaim : Prop :=
  ∀ f : LocalMap X, IsOpenHolomorphic f →
    ∀ U : Set X, f.IsWanderingComponent U →
      f.HasSimplyConnectedComponentOrbit U → ∀ z ∈ U,
        ∀ (a : X) (φ : ℕ → ℕ), StrictMono φ →
          Tendsto (fun k => f.compactifiedIterate (φ k) z) atTop
            (𝓝 (a : OnePoint X)) →
          a ∈ derivedSet f.singularValues

/-- A stronger sufficient condition, requiring a finite derived-singular
cluster point even for orbits that have an escaping subsequence. This is not
the remaining obligation for the paper's escape-or-derived-set target. -/
def WanderingOrbitClusterMeetsDerivedClaim : Prop :=
  ∀ f : LocalMap X, IsOpenHolomorphic f →
    ∀ U : Set X, f.IsWanderingComponent U →
      f.HasSimplyConnectedComponentOrbit U → ∀ z ∈ U,
        ∃ a ∈ derivedSet f.singularValues,
          ∃ φ : ℕ → ℕ, StrictMono φ ∧
            Tendsto (fun k => f.compactifiedIterate (φ k) z) atTop
              (𝓝 (a : OnePoint X))

/-- A derived singular cluster point supplies the required subsequence.  The
compact-escape alternative remains available separately, so no assertion
about all other finite cluster points is needed. -/
theorem wanderingDerivedSingularLimitClaim_of_clusterMeetsDerived
    (hcluster : WanderingOrbitClusterMeetsDerivedClaim (X := X)) :
    WanderingDerivedSingularLimitClaim (X := X) := by
  intro f hf U hU hsc z hz
  obtain ⟨a, ha, φ, hφ, hlim⟩ := hcluster f hf U hU hsc z hz
  exact ⟨φ, hφ, Or.inr ⟨a, ha, hlim⟩⟩

/-- The derived-singular cluster-point obligation only for orbits with no
subsequence escaping every compact subset of the ambient surface. -/
def NonEscapingWanderingOrbitClusterMeetsDerivedClaim : Prop :=
  ∀ f : LocalMap X, IsOpenHolomorphic f →
    ∀ U : Set X, f.IsWanderingComponent U →
      f.HasSimplyConnectedComponentOrbit U → ∀ z ∈ U,
        (¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧
          Tendsto (fun k => f.compactifiedIterate (φ k) z) atTop
            (𝓝 (∞ : OnePoint X))) →
        ∃ a ∈ derivedSet f.singularValues,
          ∃ φ : ℕ → ℕ, StrictMono φ ∧
            Tendsto (fun k => f.compactifiedIterate (φ k) z) atTop
              (𝓝 (a : OnePoint X))

/-- Separate the escape alternative before invoking the area argument.
The exact independent paper statement is preserved. -/
theorem wanderingDerivedSingularLimitClaim_of_nonEscapingClusterMeetsDerived
    (hcluster : NonEscapingWanderingOrbitClusterMeetsDerivedClaim (X := X)) :
    WanderingDerivedSingularLimitClaim (X := X) := by
  intro f hf U hU hsc z hz
  by_cases hescape : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => f.compactifiedIterate (φ k) z) atTop
        (𝓝 (∞ : OnePoint X))
  · obtain ⟨φ, hφ, hlim⟩ := hescape
    exact ⟨φ, hφ, Or.inl hlim⟩
  · obtain ⟨a, ha, φ, hφ, hlim⟩ := hcluster f hf U hU hsc z hz hescape
    exact ⟨φ, hφ, Or.inr ⟨a, ha, hlim⟩⟩

end Manifold
end SurfaceDynamics

#print axioms SurfaceDynamics.escape_or_subsequence_tendsto_mem
#print axioms SurfaceDynamics.wanderingDerivedSingularLimitClaim_of_clusterMeetsDerived
#print axioms SurfaceDynamics.wanderingDerivedSingularLimitClaim_of_nonEscapingClusterMeetsDerived
