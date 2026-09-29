module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.TrappedComponentCovering
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

/-!
# Singular values as the obstruction to covering

The finite singular values of an entire function are defined intrinsically:
a value is regular when it has an open neighbourhood over which the whole
map is a topological covering.  This makes the singular set closed by
construction and gives the global covering theorem on its complement without
adding a separate axiom.
-/

open Set Function Topology
open scoped Topology

namespace ComplexDynamics

/-- Values having a neighbourhood over which `f` is a covering map. -/
def regularValueSet (f : ℂ → ℂ) : Set ℂ :=
  {w | ∃ V : Set ℂ, IsOpen V ∧ w ∈ V ∧ IsCoveringMapOn f V}

/-- The closed set of finite singular values, characterised as the obstruction
to the global covering property. -/
def singularValues (f : ℂ → ℂ) : Set ℂ := (regularValueSet f)ᶜ

theorem isOpen_regularValueSet (f : ℂ → ℂ) : IsOpen (regularValueSet f) := by
  rw [isOpen_iff_forall_mem_open]
  intro w hw
  obtain ⟨V, hV, hwV, hcov⟩ := hw
  refine ⟨V, ?_, hV, hwV⟩
  intro y hy
  exact ⟨V, hV, hy, hcov⟩

theorem isClosed_singularValues (f : ℂ → ℂ) : IsClosed (singularValues f) :=
  (isOpen_regularValueSet f).isClosed_compl

/-- An entire map is a covering over the complement of its singular values.
This follows directly from the local definition of regular values. -/
theorem isCoveringMapOn_compl_singularValues (f : ℂ → ℂ) :
    IsCoveringMapOn f (singularValues f)ᶜ := by
  intro w hw
  have hw' : w ∈ regularValueSet f := by
    simpa only [singularValues, compl_compl] using hw
  obtain ⟨V, _hV, hwV, hcov⟩ := hw'
  exact hcov w hwV

/-- The Eremenko--Lyubich class of maps with bounded finite singular set. -/
def ClassB : Set (ℂ → ℂ) := {f | Bornology.IsBounded (singularValues f)}

def MemClassB (f : ℂ → ℂ) : Prop := f ∈ ClassB

theorem memClassB_iff (f : ℂ → ℂ) :
    MemClassB f ↔ Bornology.IsBounded (singularValues f) := Iff.rfl

end ComplexDynamics

namespace AreaDeficit

/-- A covering over the complement of the singular values is injective on a
simply connected source domain mapping into a simply connected target domain
that avoids those values. -/
theorem singular_covering_injOn_domain {f : ℂ → ℂ} {U W : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hUc : IsSimplyConnected U)
    (hW : IsOpen W) (hWc : IsSimplyConnected W)
    (hz : z ∈ U) (hf : ContinuousOn f U) (hm : MapsTo f U W)
    (havoid : W ⊆ (ComplexDynamics.singularValues f)ᶜ) :
    InjOn f U := by
  have hcov : IsCoveringMapOn (fun x : (Set.univ : Set ℂ) => f x) W := by
    have hglobal := (ComplexDynamics.isCoveringMapOn_compl_singularValues f).mono havoid
    have hc := hglobal.comp_homeomorph (Homeomorph.Set.univ ℂ)
    convert hc using 1
    funext x
    simp only [Function.comp_apply, Homeomorph.Set.univ_apply]
  exact covering_injOn_domain hU hUc hW hWc hz (subset_univ U) hf hm hcov

end AreaDeficit
