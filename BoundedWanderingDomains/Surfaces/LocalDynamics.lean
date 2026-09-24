/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Covering.Basic

/-! # Local dynamics on a Riemann surface

The map has its actual open source. Iteration is partial; `none` means that
an iterate is undefined. Normality is tested only on open sets of points
whose iterates are all defined and stay in the source. Thus the sentinel
for an undefined iterate never enters the normality condition.

For a locally compact Hausdorff surface, normality uses the unique compatible
uniformity on its one-point compactification. No metric or preferred chart
enters this definition. These are definitions and elementary structural
lemmas; no surface wandering-domain exclusion is asserted in this file.
-/

open Set Function Filter Topology
open scoped Manifold Topology

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
  exact if h : x ∈ f.source then some (f.map ⟨x, h⟩) else none

/-- Partial iterates. No value is assigned to the original map outside its source. -/
noncomputable def iterate (f : LocalMap X) : ℕ → X → Option X
  | 0, x => some x
  | n + 1, x => (f.step x).bind (f.iterate n)

@[simp] theorem iterate_zero (f : LocalMap X) (x : X) : f.iterate 0 x = some x := rfl

@[simp] theorem iterate_succ (f : LocalMap X) (n : ℕ) (x : X) (hx : x ∈ f.source) :
    f.iterate (n+1) x = f.iterate n (f.map ⟨x,hx⟩) := by
  simp [iterate, step, hx]

/-- Points whose entire orbit is defined and remains in the source. -/
def trapped (f : LocalMap X) : Set X :=
  {x | ∀ n : ℕ, ∃ y ∈ f.source, f.iterate n x = some y}

theorem trapped_subset_source (f : LocalMap X) : f.trapped ⊆ f.source := by
  intro x hx
  obtain ⟨y, hy, he⟩ := hx 0
  have hxy : x = y := Option.some.inj he
  exact hxy ▸ hy

theorem trapped_forward (f : LocalMap X) {x : X} (hx : x ∈ f.trapped) :
    f.map ⟨x, f.trapped_subset_source hx⟩ ∈ f.trapped := by
  intro n
  simpa only [iterate_succ f n x (f.trapped_subset_source hx)] using hx (n+1)

/-- The genuine self-map of the trapped set. -/
noncomputable def trappedMap (f : LocalMap X) (x : f.trapped) : f.trapped :=
  ⟨f.map ⟨x, f.trapped_subset_source x.2⟩, f.trapped_forward x.2⟩

/-- Iteration on trapped points takes values in the original surface. -/
noncomputable def orbit (f : LocalMap X) (n : ℕ) (x : f.trapped) : X :=
  ((f.trappedMap^[n]) x : X)

@[simp] theorem orbit_zero (f : LocalMap X) (x : f.trapped) : f.orbit 0 x = x := rfl

theorem orbit_mem_source (f : LocalMap X) (n : ℕ) (x : f.trapped) :
    f.orbit n x ∈ f.source := f.trapped_subset_source ((f.trappedMap^[n]) x).2

/-- Total iteration on the trapped set agrees with partial iteration. -/
theorem iterate_eq_some_orbit (f : LocalMap X) (n : ℕ) (x : f.trapped) :
    f.iterate n x = some (f.orbit n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ f n x (f.trapped_subset_source x.2)]
    exact ih (f.trappedMap x)

theorem continuous_trappedMap (f : LocalMap X) (hf : Continuous f.map) :
    Continuous f.trappedMap := by
  apply Continuous.subtype_mk
  exact hf.comp (continuous_subtype_val.subtype_mk _)

theorem continuous_orbit (f : LocalMap X) (hf : Continuous f.map) (n : ℕ) :
    Continuous (f.orbit n) :=
  continuous_subtype_val.comp ((f.continuous_trappedMap hf).iterate n)

/-- The n-th image of a set under partial iteration. -/
def imageAt (f : LocalMap X) (n : ℕ) (A : Set X) : Set X :=
  {y | ∃ x ∈ A, f.iterate n x = some y}

@[simp] theorem imageAt_zero (f : LocalMap X) (A : Set X) : f.imageAt 0 A = A := by
  ext y
  simp [imageAt]

theorem imageAt_subset_source (f : LocalMap X) {A : Set X} (hA : A ⊆ f.trapped)
    (n : ℕ) : f.imageAt n A ⊆ f.source := by
  rintro y ⟨x, hx, hxy⟩
  obtain ⟨z, hz, hxz⟩ := hA hx n
  have : y = z := Option.some.inj (hxy.symm.trans hxz)
  exact this ▸ hz

/-- The compactified partial iterate; only its restriction to trapped points
is used to formulate normality. -/
noncomputable def compactifiedIterate (f : LocalMap X) (n : ℕ) (x : X) : OnePoint X :=
  match f.iterate n x with
  | none => OnePoint.infty
  | some y => (y : OnePoint X)

/-- Compactification does not introduce an artificial value on a trapped orbit. -/
theorem compactifiedIterate_eq_orbit (f : LocalMap X) (n : ℕ) (x : f.trapped) :
    f.compactifiedIterate n x = (f.orbit n x : OnePoint X) := by
  simp [compactifiedIterate, f.iterate_eq_some_orbit n x]

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

theorem omega_subset_trapped_interior (f : LocalMap X) :
    f.omega ⊆ interior f.trapped := by
  rintro x ⟨W, hW, hx, hWT, _⟩
  exact (interior_maximal hWT hW) hx

theorem omega_subset_source (f : LocalMap X) : f.omega ⊆ f.source :=
  f.omega_subset_trapped_interior.trans (interior_subset.trans f.trapped_subset_source)

theorem isOpen_omega (f : LocalMap X) : IsOpen f.omega := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨W, hW, hx, hWT, hN⟩
  exact mem_of_superset (hW.mem_nhds hx) (fun y hy => ⟨W,hW,hy,hWT,hN⟩)

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

theorem isOpen_regularValues (f : LocalMap X) : IsOpen f.regularValues := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨W, hW, hy, hsur, hcov⟩
  exact mem_of_superset (hW.mem_nhds hy) (fun z hz => ⟨W,hW,hz,hsur,hcov⟩)

theorem isClosed_singularValues (f : LocalMap X) : IsClosed f.singularValues :=
  f.isOpen_regularValues.isClosed_compl

end LocalMap

/-- The hypotheses on the local map in the surface statements. -/
def IsOpenHolomorphic [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) : Prop :=
  IsOpenMap f.map ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map

end SurfaceDynamics
