import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Escaping components of transcendental entire functions

Statement surface for selected results of Martí-Pete, Rempe and Waterman,
*Eremenko's conjecture, wandering Lakes of Wada, and maverick points* (2025),
https://doi.org/10.1090/jams/1049. This is a scoped formalisation of published
results, not a claim to formalise the whole paper or to discover its disproof.

Theorem 1.2 realises every nonempty full compact continuum as an exact
connected escaping component. Theorem 7.1 gives the ray counterexample.
The singleton formulation explicitly disproves Eremenko's conjecture.
The Section 3 consequence obstructs curves to infinity even from fast
escaping points; connected components and path components are kept distinct.

Only Mathlib is imported. The definitions below reproduce the proof library's
definitions, making their meanings visible without importing that library.
`IsConnected` includes nonemptiness; fullness is connected plane complement.
Function iteration is written `f^[n]`. The intentionally unproved statements
in this file are the Challenge; Solution.lean supplies checked proofs with
the same names and types. Neither the library nor Solution imports Challenge.
Comparator/NanoDa verification and Palomar registration have not been run.
-/

open Set Metric Function Filter
open scoped Topology Uniformity

namespace ComplexDynamics
noncomputable section

/-- Every subsequence has a locally uniformly convergent further subsequence.
The limit has precisely the domain `U`. -/
def IsNormalSequenceOn {α β : Type*} [TopologicalSpace α] [UniformSpace β]
    (F : ℕ → α → β) (U : Set α) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ →
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ g : U → β,
      TendstoLocallyUniformly (fun n (z : U) => F (φ (ψ n)) z) g atTop

/-- Entire means complex differentiable at every finite point. -/
def IsEntire (f : ℂ → ℂ) : Prop := Differentiable ℂ f

/-- A transcendental entire map is entire and is not a polynomial function. -/
def IsTranscendentalEntire (f : ℂ → ℂ) : Prop :=
  IsEntire f ∧ ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z

/-- Escape is convergence of the orbit's Euclidean norm to positive infinity. -/
def escapingSet (f : ℂ → ℂ) : Set ℂ :=
  {z | Tendsto (fun n : ℕ => ‖(f^[n]) z‖) atTop atTop}

/-- A bounded orbit, with its bound allowed to depend on the point. -/
def boundedOrbitSet (f : ℂ → ℂ) : Set ℂ :=
  {z | ∃ R : ℝ, ∀ n : ℕ, ‖(f^[n]) z‖ ≤ R}

/-- The sphere as the one-point compactification; the map `f` stays on the plane. -/
abbrev RiemannSphere := OnePoint ℂ

instance riemannSphereUniformSpace : UniformSpace RiemannSphere :=
  uniformSpaceOfCompactR1

/-- Regard a finite iterate value as a point on the sphere. -/
def sphericalIterate (f : ℂ → ℂ) (n : ℕ) (z : ℂ) : RiemannSphere :=
  ((f^[n]) z : OnePoint ℂ)

/-- Local normality of the sphere-valued iterates. -/
def fatouSet (f : ℂ → ℂ) : Set ℂ :=
  {z | ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ IsNormalSequenceOn (sphericalIterate f) U}

/-- The Julia set is the complement of the local normality set. -/
def juliaSet (f : ℂ → ℂ) : Set ℂ := (fatouSet f)ᶜ


/-- Bungee points have an unbounded orbit which does not tend to infinity. -/
def bungeeSet (f : ℂ → ℂ) : Set ℂ := (boundedOrbitSet f ∪ escapingSet f)ᶜ

/-- Maximum modulus on the closed disk; for entire maps it equals the
maximum on the boundary circle. -/
noncomputable def maximumModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' closedBall 0 r)

/-- Escape together with a shifted orbit dominating every iterate of M at r. -/
def fastEscapingSetAtRadius (f : ℂ → ℂ) (r : ℝ) : Set ℂ :=
  {z | z ∈ escapingSet f ∧ ∃ l : ℕ, ∀ n : ℕ,
    ((maximumModulus f)^[n]) r ≤ ‖(f^[n + l]) z‖}

/-- A(f): some positive starting disk meets J(f) and gives fast escape. -/
def fastEscapingSet (f : ℂ → ℂ) : Set ℂ :=
  {z | ∃ r : ℝ, 0 < r ∧ (ball 0 r ∩ juliaSet f).Nonempty ∧ z ∈ fastEscapingSetAtRadius f r}

end
end ComplexDynamics

namespace EremenkosConjecture

/-- The closed horizontal ray starting at ζ and running to the right. -/
def horizontalRay (ζ : ℂ) : Set ℂ := {z | ζ.re ≤ z.re ∧ z.im = ζ.im}

end EremenkosConjecture

open ComplexDynamics
namespace EremenkosConjecture.Palomar

/-- Eremenko's conjecture fails: there is a transcendental entire function
with an escaping point whose only connected escaping subset is its singleton. -/
theorem eremenko_conjecture_false : ∃ (f : ℂ → ℂ) (z : ℂ),
    IsTranscendentalEntire f ∧ z ∈ escapingSet f ∧
      ∀ A : Set ℂ, IsConnected A → A ⊆ escapingSet f → z ∈ A → A = {z} := by
  sorry

/-- Theorem 1.2: every nonempty full compact continuum is exactly a connected
component of the escaping set of a transcendental entire function. -/
theorem theorem_1_2 (X : Set ℂ) (hX : IsCompact X) (hconn : IsConnected X)
    (hfull : IsConnected Xᶜ) :
    ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧ ∃ z ∈ escapingSet f,
      connectedComponentIn (escapingSet f) z = X := by
  sorry

/-- Theorem 7.1: the nonnegative real ray is Julia, its endpoint escapes,
the positive ray is bungee, and the indicated connected components are exact. -/
theorem theorem_7_1 : ∃ f : ℂ → ℂ,
    IsTranscendentalEntire f ∧ horizontalRay 0 ⊆ juliaSet f ∧ (0 : ℂ) ∈ escapingSet f ∧
    horizontalRay 0 \ {0} ⊆ bungeeSet f ∧
    connectedComponentIn (juliaSet f ∪ escapingSet f ∪ bungeeSet f) 0 = horizontalRay 0 ∧
    connectedComponentIn (escapingSet f) 0 = {0} := by
  sorry

/-- Counterexamples to the strong (curve-to-infinity) version, not the original connected-component conjecture. -/
theorem no_escaping_curve_to_infinity (K : Set ℂ) (hK : IsCompact K)
    (hconn : IsConnected K) (hfull : IsConnected Kᶜ) :
    ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧ K ⊆ fastEscapingSet f ∧
      (∀ x ∈ K, pathComponentIn (escapingSet f) x = pathComponentIn K x) ∧
      (∀ x ∈ frontier K, pathComponentIn (juliaSet f) x = pathComponentIn (frontier K) x) ∧
      (∀ γ : ℝ → ℂ, ContinuousOn γ (Ici 0) → γ 0 ∈ K → MapsTo γ (Ici 0) (escapingSet f) →
        ¬ Tendsto (fun t => ‖γ t‖) atTop atTop) := by
  sorry

end EremenkosConjecture.Palomar
