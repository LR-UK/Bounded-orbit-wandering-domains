/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.Statements

/-! # Topological reduction for the derived-singular-limit theorem

The compactification alternative is purely topological.  This file isolates
the remaining analytic statement: every finite subsequential limit of a
wandering orbit belongs to the derived singular set. -/

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
      Tendsto (u ∘ φ) atTop (𝒩 a) → a ∈ S) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (Tendsto (fun k => (u (φ k) : OnePoint X)) atTop
          (𝒩 (∞ : OnePoint X)) ∨
        ∃ a ∈ S, Tendsto (fun k => (u (φ k) : OnePoint X)) atTop
          (𝒩 (a : OnePoint X))) := by
  rcases escape_or_convergent_subsequence u with hesc | ⟨a,φ,hφ,hlim⟩
  · refine ⟨id, strictMono_id, Or.inl ?_⟩
    simpa only [id_eq] using hesc
  · refine ⟨φ,hφ,Or.inr ⟨a,hfinite a φ hφ hlim,?_⟩⟩
    exact continuous_coe.tendsto.comp hlim

variable [LocallyCompactSpace X]

/-- Every point of a wandering normality component is trapped, so its partial
iterates are genuine points of the surface. -/
theorem LocalMap.IsWanderingComponent.subset_trapped (f : LocalMap X)
    {U : Set X} (hU : f.IsWanderingComponent U) : U ⊆ f.trapped := by
  rintro z hz
  obtain ⟨V,hV0,hcomp,_,_⟩ := hU
  obtain ⟨w,hw,hVw⟩ := hcomp 0
  apply f.omega_subset_trapped_interior.trans interior_subset
  rw [← hV0]
  exact hVw ▸ connectedComponentIn_subset f.omega w hz

section Manifold

variable [ChartedSpace ℂ X] [SecondCountableTopology X] [ConnectedSpace X]
  [IsManifold 𝒘(ℂ) 1 X]

/-- The analytic core left after the compactification argument: every finite
subsequential limit of a simply-connected wandering orbit is a derived
singular value. -/
def FiniteWanderingOrbitLimitsDerivedClaim : Prop :=
  ∀ f : LocalMap X, IsOpenHolomorphic f →
    ∀ U : Set X, f.IsWanderingComponent U →
      f.HasSimplyConnectedComponentOrbit U → ∀ z ∈ U,
        ∀ (a : X) (φ : ℕ → ℕ), StrictMono φ →
          Tendsto (fun k => f.compactifiedIterate (φ k) z) atTop
            (𝒩 (a : OnePoint X)) →
          a ∈ derivedSet f.singularValues

/-- The finite-limit analytic claim implies the full Theorem 1.5 statement.
No normal-family or metric argument is hidden in this implication. -/
theorem wanderingDerivedSingularLimitClaim_of_finiteLimits
    (hfinite : FiniteWanderingOrbitLimitsDerivedClaim (X := X)) :
    WanderingDerivedSingularLimitClaim (X := X) := by
  intro f hf U hU hsc z hz
  let zt : f.trapped := ⟨z, hU.subset_trapped f hz⟩
  obtain ⟨φ,hφ,hφlim⟩ := escape_or_subsequence_tendsto_mem
    (derivedSet f.singularValues) (fun n => f.orbit n zt) (by
      intro a ψ hψ hlim
      apply hfinite f hf U hU hsc z hz a ψ hψ
      have hcoe := continuous_coe.tendsto.comp hlim
      simpa only [f.compactifiedIterate_eq_orbit] using hcoe)
  refine ⟨φ,hφ,?_⟩
  simpa only [f.compactifiedIterate_eq_orbit] using hφlim

end Manifold
end SurfaceDynamics

#print axioms SurfaceDynamics.escape_or_subsequence_tendsto_mem
#print axioms SurfaceDynamics.wanderingDerivedSingularLimitClaim_of_finiteLimits
