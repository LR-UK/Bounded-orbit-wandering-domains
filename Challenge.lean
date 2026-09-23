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

/-!
# Absence of bounded-orbit wandering domains

This Challenge is independent of the proof development. Its imports are
Mathlib only. The two deliberate theorem holes are supplied by Solution.

The classical hyperbolic metric facts are proved in the Solution development,
including disc-covering existence and the total-area formula. Neither theorem
assumes a metric-existence, covering-existence or area-formula hypothesis.

Two results are stated:
1. For a locally defined analytic map, an orbit of simply connected
   components of the maximal trapped open set cannot be both compactly
   contained and wandering, under eventual injectivity on large discs.
2. For a transcendental entire map, a Fatou component containing one point
   with bounded forward orbit cannot be wandering. No boundedness of whole
   components, simple connectivity or injectivity is assumed in this theorem.

In (2), boundedness is precisely boundedness of the set {f^[n](z) : n ∈ ℕ}.
Simple connectivity and eventual disc injectivity are explicit hypotheses
only in (1); the proof of (2) derives the corresponding properties for
auxiliary trapped components and their intrinsic discs.

The intrinsic discs use a normalized Riemann coordinate. Their definition
is independent of that coordinate (proved in the Solution development).
The starting time may depend on the disc radius.

Mathlib supplies differentiability, analyticity, iteration, connected
components, simple connectivity, boundedness, measures and convergence.
Neither the pinned Mathlib nor the available Tau Ceti sources supplies the
Fatou-component definitions needed here. The short definitions below are
copied from the supplied ComplexDynamics repository and compared against
those same declarations in the Solution. No value of f at infinity is used.

Mathematical direction: Lasse Rempe. AI-assisted formalisation: OpenAI
ChatGPT/Codex. The proof dependencies retain their separate attribution.
This is the substantive development, not a wrapper around a previously
registered theorem. Global derived-singular-set statements are not claimed.
-/

open Set Metric Function Filter
open scoped Topology Uniformity

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

namespace BoundedWanderingDomains

/-- The interior of the set of points whose entire forward orbit stays
in V. The values of the total function outside V play no role. -/
def trappedInterior (f : ℂ → ℂ) (V : Set ℂ) : Set ℂ :=
  interior {z | ∀ n : ℕ, f^[n] z ∈ V}

/-- Eventually injective on each fixed intrinsic disc about the orbit
point. The radius parameter r is in (0,1) in a normalized Riemann chart;
the corresponding curvature −1 radius is 2 artanh r. N may depend on r. -/
def EventuallyInjectiveOnLargeDiscs (f : ℂ → ℂ) (U : ℕ → Set ℂ) (z : ℕ → ℂ) : Prop :=
  ∀ r : ℝ, 0 < r → r < 1 → ∃ N : ℕ, ∀ n ≥ N, ∃ u : ℂ → ℂ,
    DifferentiableOn ℂ u (U n) ∧ BijOn u (U n) (ball 0 1) ∧ u (z n) = 0 ∧
      InjOn f (U n ∩ u ⁻¹' ball 0 r)

end BoundedWanderingDomains


namespace BoundedWanderingDomains

/-- LOCAL THEOREM. Analyticity is needed only near closure(V). The U_n are
the components of the maximal trapped open set through f^[n](z).
A compact K inside V contains the entire component orbit. Under eventual disc injectivity, these components cannot
be pairwise disjoint. -/
theorem no_local_bounded_wandering_domains
    {f : ℂ → ℂ} {V K : Set ℂ} {z : ℂ} {U : ℕ → Set ℂ}
    (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hf : AnalyticOnNhd ℂ f (closure V))
    (hn : ∀ x ∈ closure V, ¬EventuallyConst f (𝓝 x))
    (hK : IsCompact K) (hKV : K ⊆ V)
    (hz : z ∈ trappedInterior f V)
    (hU : ∀ n, U n = connectedComponentIn (trappedInterior f V) (f^[n] z))
    (hsc : ∀ n, IsSimplyConnected (U n))
    (hbounded : ∀ n, U n ⊆ K)
    (hinj : EventuallyInjectiveOnLargeDiscs f U (fun n => f^[n] z)) :
    ¬ Pairwise (fun n m : ℕ => Disjoint (U n) (U m)) := by
  sorry

/-- ENTIRE THEOREM. A transcendental entire function cannot have a wandering
Fatou component containing a point z with bounded forward orbit.
The bounded set is only {f^[n](z) : n ∈ ℕ}; no bound on the union of
Fatou components is assumed. Simple connectivity of auxiliary trapped
components and eventual injectivity on intrinsic discs are proved.
The proof constructs the required hyperbolic metrics with curvature −1. -/
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
