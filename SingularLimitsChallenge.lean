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
# Derived singular limit functions of entire wandering domains

For every wandering Fatou component of a transcendental entire function,
a subsequence of iterates converges locally uniformly, in the spherical
metric, to a constant in the derived set of the spherical singular values.
This is convergence of functions on the original component, and hence of
every point orbit along the same subsequence; it is not convergence of domains.
The statement is existential and does not classify every limit function.

Neither simple connectivity nor injectivity along the orbit is assumed.
Infinity belongs to the spherical singular set. All dynamics remain plane-valued.
No extension to locally defined maps or meromorphic functions is claimed.

This statement file imports Mathlib only and is independent of the proof.
Its nine definitions are compared with the proof development, including
normality and singular values. The one deliberate theorem hole is supplied
by SingularLimitsSolution. Mathematical direction: Lasse Rempe; paper authors:
Nikolai Prochorov, Lasse Rempe and James Waterman. AI-assisted formalisation:
OpenAI ChatGPT/Codex. See formalization.yaml for proof provenance and scope.
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

attribute [instance] instCommCStarAlgebraComplex

end Definitions

namespace BoundedWanderingDomains

/-- A constant subsequential limit function in the derived spherical singular set. -/
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

end BoundedWanderingDomains
