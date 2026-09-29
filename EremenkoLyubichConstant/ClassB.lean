module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

/-!
# The Eremenko--Lyubich class

This file gives a covering-theoretic definition of singular values.  It is deliberately
formulated first for arbitrary maps of topological spaces, so that it can later be moved to
a general function-theory or complex-dynamics library.

A point is singular precisely when it has no evenly covered neighbourhood.  For an entire
function, membership in class `B` means that the function is transcendental and its set of
singular values is bounded.
-/

open Metric Set

namespace FunctionTheory

section Topological

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

/-- A singular value of a map is a point with no evenly covered neighbourhood. -/
def IsSingularValue (f : E → X) (y : X) : Prop :=
  ¬IsEvenlyCovered f y (f ⁻¹' {y})

/-- The set of singular values of a map, defined covering-theoretically. -/
def singularValueSet (f : E → X) : Set X :=
  {y | IsSingularValue f y}

/-- A point is nonsingular exactly when it is evenly covered. -/
theorem not_isSingularValue_iff {f : E → X} {y : X} :
    ¬IsSingularValue f y ↔ IsEvenlyCovered f y (f ⁻¹' {y}) := by
  simp [IsSingularValue]

/-- A map is a covering over `s` exactly when `s` contains no singular value. -/
theorem isCoveringMapOn_iff_disjoint_singularValueSet {f : E → X} {s : Set X} :
    IsCoveringMapOn f s ↔ Disjoint s (singularValueSet f) := by
  rw [Set.disjoint_left]
  simp only [IsCoveringMapOn, singularValueSet, mem_ofPred_eq, IsSingularValue, not_not]

end Topological

section Entire

/-- A complex-valued function is represented by a polynomial. -/
def IsPolynomialFunction (f : ℂ → ℂ) : Prop :=
  ∃ p : Polynomial ℂ, f = fun z ↦ p.eval z

/-- A transcendental entire function is an entire function which is not a polynomial. -/
def IsTranscendentalEntire (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ ¬IsPolynomialFunction f

/-- Membership in the Eremenko--Lyubich class `B` of transcendental entire functions. -/
def MemClassB (f : ℂ → ℂ) : Prop :=
  IsTranscendentalEntire f ∧ Bornology.IsBounded (singularValueSet f)

/-- Membership in the Speiser class `S` of transcendental entire functions with finitely many
singular values. -/
def MemClassS (f : ℂ → ℂ) : Prop :=
  IsTranscendentalEntire f ∧ (singularValueSet f).Finite

/-- The Eremenko--Lyubich class of transcendental entire functions. -/
def ClassB : Set (ℂ → ℂ) := {f | MemClassB f}

/-- The Speiser class of transcendental entire functions. -/
def ClassS : Set (ℂ → ℂ) := {f | MemClassS f}

/-- Compatibility with the predicate spelling of class-B membership. -/
@[simp] theorem mem_ClassB {f : ℂ → ℂ} : f ∈ ClassB ↔ MemClassB f := Iff.rfl

/-- Compatibility with the predicate spelling of Speiser-class membership. -/
@[simp] theorem mem_ClassS {f : ℂ → ℂ} : f ∈ ClassS ↔ MemClassS f := Iff.rfl

/-- Every Speiser-class entire function belongs to the Eremenko--Lyubich class. -/
theorem MemClassS.memClassB {f : ℂ → ℂ} (hf : MemClassS f) : MemClassB f :=
  ⟨hf.1, hf.2.isBounded⟩

/-- The Speiser class is contained in the Eremenko--Lyubich class. -/
theorem classS_subset_classB : ClassS ⊆ ClassB := fun _ hf ↦ hf.memClassB

/-- Boundedness of the singular set is equivalent to the existence of a positive radius
outside which the function is a covering map. -/
theorem isBounded_singularValueSet_iff_exists_isCoveringMapOn_exterior (f : ℂ → ℂ) :
    Bornology.IsBounded (singularValueSet f) ↔
      ∃ R : ℝ, 0 < R ∧ IsCoveringMapOn f {z : ℂ | R < ‖z‖} := by
  constructor
  · intro h
    obtain ⟨R, hR, hsub⟩ := h.subset_ball_lt 0 0
    refine ⟨R, hR, ?_⟩
    intro y hy
    by_contra hnot
    have hsing : y ∈ singularValueSet f := hnot
    have hyball := hsub hsing
    rw [mem_ball_zero_iff] at hyball
    exact (not_lt_of_ge (le_of_lt hy)) hyball
  · rintro ⟨R, _hR, hcover⟩
    refine (isBounded_closedBall : Bornology.IsBounded (closedBall (0 : ℂ) R)).subset ?_
    intro y hy
    rw [mem_closedBall_zero_iff]
    by_contra hnot
    have hyext : R < ‖y‖ := lt_of_not_ge hnot
    exact hy (hcover y hyext)

/-- The exterior-covering characterisation of the Eremenko--Lyubich class. -/
theorem memClassB_iff_exists_isCoveringMapOn_exterior (f : ℂ → ℂ) :
    MemClassB f ↔ IsTranscendentalEntire f ∧
      ∃ R : ℝ, 0 < R ∧ IsCoveringMapOn f {z : ℂ | R < ‖z‖} := by
  rw [MemClassB, isBounded_singularValueSet_iff_exists_isCoveringMapOn_exterior]

end Entire

end FunctionTheory
