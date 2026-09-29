module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.SphericalSingularValues

@[expose] public section

/-! # Singular values of the restriction to an actual open domain -/

open Set Function Topology OnePoint
open scoped Topology

namespace ComplexDynamics

def regularValueSetOn (f : ℂ → ℂ) (V : Set ℂ) : Set ℂ :=
  {w | ∃ W : Set ℂ, IsOpen W ∧ w ∈ W ∧
    IsCoveringMapOn (fun x : V => f x) W}

def singularValuesOn (f : ℂ → ℂ) (V : Set ℂ) : Set ℂ :=
  (regularValueSetOn f V)ᶜ

def sphericalSingularValuesOn (f : ℂ → ℂ) (V : Set ℂ) : Set (OnePoint ℂ) :=
  insert ∞ (((↑) : ℂ → OnePoint ℂ) '' singularValuesOn f V)

theorem isOpen_regularValueSetOn (f : ℂ → ℂ) (V : Set ℂ) :
    IsOpen (regularValueSetOn f V) := by
  rw [isOpen_iff_forall_mem_open]
  rintro w ⟨W, hW, hw, hc⟩
  exact ⟨W, fun y hy => ⟨W, hW, hy, hc⟩, hW, hw⟩

theorem isClosed_singularValuesOn (f : ℂ → ℂ) (V : Set ℂ) :
    IsClosed (singularValuesOn f V) := (isOpen_regularValueSetOn f V).isClosed_compl

theorem isCoveringMapOn_compl_singularValuesOn (f : ℂ → ℂ) (V : Set ℂ) :
    IsCoveringMapOn (fun x : V => f x) (singularValuesOn f V)ᶜ := by
  intro w hw
  have hw' : w ∈ regularValueSetOn f V := by simpa [singularValuesOn] using hw
  obtain ⟨W, _, hw, hc⟩ := hw'
  exact hc w hw

theorem derivedSet_sphericalSingularValuesOn (f : ℂ → ℂ) (V : Set ℂ) :
    derivedSet (sphericalSingularValuesOn f V) =
      BoundedWanderingDomains.sphericalDerivedSet (singularValuesOn f V) := by
  have hs : derivedSet ({∞} : Set (OnePoint ℂ)) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (Set.Infinite.of_accPt hx) (finite_singleton _)
  rw [sphericalSingularValuesOn, ← singleton_union, derivedSet_union, hs, empty_union]
  rfl

/-- Values outside V are irrelevant to the restricted singular set. -/
theorem singularValuesOn_congr {f g : ℂ → ℂ} {V : Set ℂ} (h : EqOn f g V) :
    singularValuesOn f V = singularValuesOn g V := by
  have he : (fun x : V => f x) = (fun x : V => g x) := funext (fun x => h x.property)
  simp only [singularValuesOn, regularValueSetOn, he]

end ComplexDynamics
