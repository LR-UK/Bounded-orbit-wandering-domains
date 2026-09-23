/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The spherical and Fatou-set definitions adapt LR-UK/exp-chaotic.
-/
import ComplexDynamics.Normality
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Connected.LocallyConnected

open Function Filter Set Metric
open scoped Topology Uniformity

namespace ComplexDynamics

noncomputable section

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

/-- Uniform escape of a set, including the empty set. -/
def EscapesUniformlyOn (f : ℂ → ℂ) (K : Set ℂ) : Prop :=
  ∀ R : ℝ, ∀ᶠ n : ℕ in atTop, ∀ z ∈ K, R < ‖(f^[n]) z‖

/-- The sphere as the one-point compactification; the map `f` stays on the plane. -/
abbrev RiemannSphere := OnePoint ℂ

instance riemannSphereUniformSpace : UniformSpace RiemannSphere :=
  uniformSpaceOfCompactR1

def sphericalIterate (f : ℂ → ℂ) (n : ℕ) (z : ℂ) : RiemannSphere :=
  ((f^[n]) z : OnePoint ℂ)

/-- Local normality of the sphere-valued iterates. -/
def fatouSet (f : ℂ → ℂ) : Set ℂ :=
  {z | ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ IsNormalSequenceOn (sphericalIterate f) U}

def juliaSet (f : ℂ → ℂ) : Set ℂ := (fatouSet f)ᶜ

def IsFatouComponent (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∃ z ∈ fatouSet f, U = connectedComponentIn (fatouSet f) z

/-- A Fatou component is wandering when no two forward images belong to the
same Fatou component. This is stated using the component containing each image. -/
def IsWanderingDomain (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  IsFatouComponent f U ∧ ∀ z ∈ U, ∀ n m : ℕ, n ≠ m →
    connectedComponentIn (fatouSet f) ((f^[n]) z) ≠
      connectedComponentIn (fatouSet f) ((f^[m]) z)

theorem isOpen_fatouSet (f : ℂ → ℂ) : IsOpen (fatouSet f) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨U, hU, hz, hnormal⟩
  exact Filter.mem_of_superset (hU.mem_nhds hz) (fun w hw => ⟨U, hU, hw, hnormal⟩)

theorem isClosed_juliaSet (f : ℂ → ℂ) : IsClosed (juliaSet f) :=
  (isOpen_fatouSet f).isClosed_compl

theorem mem_fatouSet_iff_exists_ball {f : ℂ → ℂ} {z : ℂ} :
    z ∈ fatouSet f ↔ ∃ r : ℝ, 0 < r ∧
      IsNormalSequenceOn (sphericalIterate f) (ball z r) := by
  constructor
  · rintro ⟨U, hU, hz, hnormal⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z hz
    exact ⟨r, hr, hnormal.mono hball⟩
  · rintro ⟨r, hr, hnormal⟩
    exact ⟨ball z r, isOpen_ball, mem_ball_self hr, hnormal⟩

theorem EscapesUniformlyOn.mono {f : ℂ → ℂ} {K L : Set ℂ}
    (h : EscapesUniformlyOn f K) (hLK : L ⊆ K) : EscapesUniformlyOn f L := by
  intro R
  exact (h R).mono fun _ hn z hz => hn z (hLK hz)

theorem EscapesUniformlyOn.subset_escapingSet {f : ℂ → ℂ} {K : Set ℂ}
    (h : EscapesUniformlyOn f K) : K ⊆ escapingSet f := by
  intro z hz
  exact tendsto_atTop.2 fun R => (h R).mono fun _ hn => (hn z hz).le

theorem disjoint_boundedOrbitSet_escapingSet (f : ℂ → ℂ) :
    Disjoint (boundedOrbitSet f) (escapingSet f) := by
  rw [Set.disjoint_left]
  rintro z ⟨R, hR⟩ hz
  obtain ⟨n, hn⟩ := (hz.eventually (eventually_gt_atTop R)).exists
  exact (not_lt_of_ge (hR n)) hn

end
end ComplexDynamics
