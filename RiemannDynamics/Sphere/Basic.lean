/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-!
# The Riemann sphere

The Riemann sphere `ℂ̂` is `OnePoint ℂ` — the one-point compactification of `ℂ`,
with a single added point `∞`. We commit to working concretely on this object
with two explicit coordinate charts:

* `chartFinite`, the identity chart on `{z : ℂ̂ | z ≠ ∞}`;
* `chartInfty`, the chart `z ↦ 1/z` (sending `∞ ↦ 0`) on `{z : ℂ̂ | z ≠ 0}`.

We do not introduce an abstract Riemann-surface structure at this point — see
`Uniformization/` for the lift to general Riemann surfaces.

## Main definitions

* `ℂ̂` — notation for the Riemann sphere `OnePoint ℂ`.
* `chartFiniteMap`, `chartInftyMap` — the two chart maps `ℂ̂ → ℂ`.
* `chartFiniteSource`, `chartInftySource` — the corresponding open source sets.

## Main results

* `chartSource_union_eq_univ`, `chartSource_inter_eq` — the two chart sources
  cover `ℂ̂`, and their overlap is `ℂ̂ \ {0, ∞}`.
* `chart_transition_holomorphic` — the transition map `z ↦ z⁻¹` is holomorphic.
* `isOpen_chartFiniteSource`, `isOpen_chartInftySource` — the chart sources are
  open.
-/

open OnePoint Topology

namespace RiemannDynamics

/-- The Riemann sphere `ℂ̂` as the one-point compactification of `ℂ`. -/
notation "ℂ̂" => OnePoint ℂ

/-! ## Basic instances on `ℂ̂`

Mathlib supplies these automatically because `ℂ` is a locally compact Hausdorff
connected space; we record them as documentation that the expected structure is
present. -/

example : CompactSpace ℂ̂ := inferInstance
example : T2Space ℂ̂ := inferInstance

/-! ## The two coordinate charts

We define each chart as a plain map `ℂ̂ → ℂ` together with the underlying open
source set. Bundling them into `OpenPartialHomeomorph` is straightforward but
adds bookkeeping; we keep the unbundled form here because downstream usage in
the dynamics line only ever needs the chart maps composed with `DifferentiableOn ℂ`. -/

/-- The finite chart, defined on `{z : ℂ̂ | z ≠ ∞}` and sending `(↑w) ↦ w`.
At `∞` we set the value to `0` for total definedness; downstream lemmas restrict
to the chart's source. -/
noncomputable def chartFiniteMap : ℂ̂ → ℂ := fun z =>
  match z with
  | (w : ℂ) => w
  | ∞ => 0

/-- The infinity chart, defined on `{z : ℂ̂ | z ≠ 0}` and sending
`(↑w) ↦ w⁻¹`, `∞ ↦ 0`. Outside the source (at `z = 0`) the value is `0` for
total definedness; downstream lemmas restrict to the chart's source. -/
noncomputable def chartInftyMap : ℂ̂ → ℂ := fun z =>
  match z with
  | (w : ℂ) => w⁻¹
  | ∞ => 0

/-- The source of the finite chart: every point except `∞`. -/
def chartFiniteSource : Set ℂ̂ := {z | z ≠ ∞}

/-- The source of the infinity chart: every point except `0`. -/
def chartInftySource : Set ℂ̂ := {z | z ≠ ((0 : ℂ) : ℂ̂)}

/-- The two chart sources cover `ℂ̂`. -/
theorem chartSource_union_eq_univ :
    chartFiniteSource ∪ chartInftySource = Set.univ := by
  ext z
  simp only [chartFiniteSource, chartInftySource, Set.mem_union, Set.mem_ofPred_eq,
    Set.mem_univ, iff_true]
  by_cases h : z = ∞
  · subst h
    right
    exact OnePoint.infty_ne_coe (0 : ℂ)
  · left
    exact h

/-- The two chart sources overlap exactly on `ℂ̂ \ {0, ∞}`. -/
theorem chartSource_inter_eq :
    chartFiniteSource ∩ chartInftySource =
      {z : ℂ̂ | z ≠ ((0 : ℂ) : ℂ̂) ∧ z ≠ ∞} := by
  ext z
  simp only [chartFiniteSource, chartInftySource, Set.mem_inter_iff, Set.mem_ofPred_eq]
  tauto

/-- The transition map between the two charts on the overlap is `z ↦ z⁻¹` on
`ℂ \ {0}`, which is holomorphic. -/
theorem chart_transition_holomorphic :
    DifferentiableOn ℂ (fun z : ℂ => z⁻¹) {z : ℂ | z ≠ 0} :=
  differentiableOn_inv

/-- The finite chart is open. -/
theorem isOpen_chartFiniteSource : IsOpen chartFiniteSource := by
  have h : chartFiniteSource = Set.range ((↑) : ℂ → ℂ̂) := by
    ext z
    simp only [chartFiniteSource, Set.mem_ofPred_eq, Set.mem_range]
    exact OnePoint.ne_infty_iff_exists
  rw [h]
  exact OnePoint.isOpen_range_coe

/-- The infinity chart is open. -/
theorem isOpen_chartInftySource : IsOpen chartInftySource := by
  have h : chartInftySource = ({((0 : ℂ) : ℂ̂)} : Set ℂ̂)ᶜ := by
    ext z
    simp only [chartInftySource, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
  rw [h]
  exact isClosed_singleton.isOpen_compl

end RiemannDynamics
