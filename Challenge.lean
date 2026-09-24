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

/-!
# Main statements: wandering domains and derived singular limit functions

Independent statement file: only Mathlib is imported. The six deliberate
statement holes are supplied by Solution, and their types and all supporting
definitions are checked by the comparator configuration.

The global theorems include locally uniform escape to infinity and both
pointwise and locally uniform derived-singular limit formulations. The local
statements in this checkpoint are the proved planar versions: bounded trapped
components, and the simply connected local singular-limit theorem. The proposed
arbitrary-surface extensions remain research work and are not claimed here.

No entire map is evaluated at infinity. Hyperbolic areas use curvature -1.
Mathematical direction: Lasse Rempe. Paper authors: Nikolai Prochorov,
Lasse Rempe and James Waterman. AI-assisted formalisation: OpenAI ChatGPT/Codex.
-/

open Set Metric Function Filter OnePoint Topology
open scoped Topology Uniformity

section Definitions

-- Match the instance environment of the original defining modules.
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

namespace ComplexDynamics

def regularValueSetOn (f : ℂ → ℂ) (V : Set ℂ) : Set ℂ :=
  {w | ∃ W : Set ℂ, IsOpen W ∧ w ∈ W ∧
    IsCoveringMapOn (fun x : V => f x) W}

def singularValuesOn (f : ℂ → ℂ) (V : Set ℂ) : Set ℂ :=
  (regularValueSetOn f V)ᶜ

def sphericalSingularValuesOn (f : ℂ → ℂ) (V : Set ℂ) : Set (OnePoint ℂ) :=
  insert ∞ (((↑) : ℂ → OnePoint ℂ) '' singularValuesOn f V)

end ComplexDynamics

namespace BoundedWanderingDomains

/-- Interior of the points whose entire forward orbit stays in V. -/
def trappedInterior (f : ℂ → ℂ) (V : Set ℂ) : Set ℂ :=
  interior {z | ∀ n : ℕ, f^[n] z ∈ V}

end BoundedWanderingDomains

attribute [instance] instCommCStarAlgebraComplex

end Definitions

namespace BoundedWanderingDomains

theorem no_local_bounded_wandering_domains
    {f : ℂ → ℂ} {V K : Set ℂ} {z : ℂ} {U : ℕ → Set ℂ}
    (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hf : AnalyticOnNhd ℂ f (closure V))
    (hn : ∀ x ∈ closure V, ¬EventuallyConst f (𝓝 x))
    (hK : IsCompact K) (hKV : K ⊆ V)
    (hz : z ∈ trappedInterior f V)
    (hU : ∀ n, U n = connectedComponentIn (trappedInterior f V) (f^[n] z))
    (hbounded : ∀ n, f^[n] z ∈ K) :
    ¬ Pairwise (fun n m : ℕ => Disjoint (U n) (U m)) := by
  sorry

theorem no_bounded_wandering_domains_transcendental_entire
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hbounded : Bornology.IsBounded (Set.range (fun n : ℕ => (f^[n]) z))) :
    ¬ Pairwise (fun n m : ℕ => Disjoint (U n) (U m)) := by
  sorry

theorem wandering_orbit_locallyUniform_infty
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n+1)))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ TendstoLocallyUniformlyOn
      (fun k w => ((f^[φ k]) w : OnePoint ℂ))
      (fun _ => (∞ : OnePoint ℂ)) atTop (U 0) := by
  sorry

theorem wandering_orbit_pointwise_spherical_singular_derivedSet
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n+1)))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m))) :
    ∃ a ∈ derivedSet (ComplexDynamics.sphericalSingularValues f), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto
        (fun k => ((f^[φ k]) z : OnePoint ℂ)) atTop (𝓝 a) := by
  sorry

theorem wandering_orbit_locallyUniform_spherical_singular_derivedSet
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n+1)))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m))) :
    ∃ a ∈ derivedSet (ComplexDynamics.sphericalSingularValues f), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ TendstoLocallyUniformlyOn
        (fun k w => ((f^[φ k]) w : OnePoint ℂ)) (fun _ => a) atTop (U 0) := by
  sorry

attribute [-instance] instCommCStarAlgebraComplex

theorem local_wandering_orbit_locallyUniform_singular_derivedSet
    {f : ℂ → ℂ} {V : Set ℂ} {z : ℂ} {U : ℕ → Set ℂ}
    (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hf : AnalyticOnNhd ℂ f (closure V))
    (hn : ∀ x ∈ closure V, ¬EventuallyConst f (𝓝 x))
    (hz : z ∈ trappedInterior f V)
    (hU : ∀ n, U n = connectedComponentIn (trappedInterior f V) (f^[n] z))
    (hsc : ∀ n, IsSimplyConnected (U n))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m))) :
    ∃ a ∈ closure V, (a : OnePoint ℂ) ∈ derivedSet (ComplexDynamics.sphericalSingularValuesOn f V) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoLocallyUniformlyOn (fun k w => (f^[φ k]) w) (fun _ => a) atTop (U 0) := by
  sorry

attribute [instance] instCommCStarAlgebraComplex

end BoundedWanderingDomains
