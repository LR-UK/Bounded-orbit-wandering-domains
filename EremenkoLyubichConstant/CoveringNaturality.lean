module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

open Function Set

namespace Path.Homotopic.Quotient

/-- Changing a continuous map transports the endpoints of the mapped path class. -/
theorem map_congr_cast {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {a b : E} (Γ : Path.Homotopic.Quotient a b) {f g : C(E, F)} (h : f = g) :
    Γ.map f = (Γ.map g).cast (congrArg (fun k : C(E, F) ↦ k a) h)
      (congrArg (fun k : C(E, F) ↦ k b) h) := by
  subst g
  simp

end Path.Homotopic.Quotient

namespace FundamentalGroup

/-- Change the basepoint by equality, with an explicit action on loop classes. -/
noncomputable def castEquiv {X : Type*} [TopologicalSpace X] {x y : X} (h : x = y) :
    FundamentalGroup X x ≃* FundamentalGroup X y := by
  subst y
  exact MulEquiv.refl _

/-- Equality transport acts on a loop by transporting both endpoints. -/
@[simp] theorem castEquiv_apply {X : Type*} [TopologicalSpace X] {x y : X} (h : x = y)
    (γ : FundamentalGroup X x) : castEquiv h γ = γ.toPath.cast h.symm h.symm := by
  subst y
  simp [castEquiv]

/-- The based induced map needs no transport when the basepoint equality is reflexive. -/
@[simp] theorem mapOfEq_rfl {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (p : C(E, X)) (e : E) : mapOfEq p (rfl : p e = p e) = map p e := by
  ext γ
  simp [mapOfEq_apply, map_apply]

/-- Successive equality transports compose on the induced fundamental-group map. -/
theorem castEquiv_comp_mapOfEq {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (p : C(E, X)) {e : E} {x y : X} (h : p e = x) (k : x = y) :
    (castEquiv k).toMonoidHom.comp (mapOfEq p h) = mapOfEq p (h.trans k) := by
  ext γ
  simp [mapOfEq_apply]

/-- Reverse the basepoint transport in an inclusion between covering subgroups. -/
theorem range_mapOfEq_le_iff
    {E F X : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
    (p : C(E, X)) (q : C(F, X)) (e : E) (f : F) (h : q f = p e) :
    (mapOfEq q h).range ≤ (map p e).range ↔
      (map q f).range ≤ (mapOfEq p h.symm).range := by
  constructor
  · intro hh γ hγ
    obtain ⟨a, rfl⟩ := hγ
    obtain ⟨b, hb⟩ := hh (show mapOfEq q h a ∈ (mapOfEq q h).range from ⟨a, rfl⟩)
    refine ⟨b, ?_⟩
    rw [mapOfEq_apply]
    change (map p e b).toPath.cast h h = _
    rw [hb, mapOfEq_apply]
    simp
  · intro hh γ hγ
    obtain ⟨a, rfl⟩ := hγ
    obtain ⟨b, hb⟩ := hh (show map q f a ∈ (map q f).range from ⟨a, rfl⟩)
    refine ⟨b, ?_⟩
    have hh := congrArg (fun γ : FundamentalGroup X (q f) ↦ γ.toPath.cast h.symm h.symm) hb
    simpa only [mapOfEq_apply, map_apply, Path.Homotopic.Quotient.cast_cast,
      Path.Homotopic.Quotient.cast_rfl_rfl] using hh

end FundamentalGroup

namespace IsCoveringMap

/-- Transporting the endpoints does not change the endpoint of a lifted path. -/
theorem monodromy_cast_val
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hp : IsCoveringMap p) {x y x' y' : X}
    (γ : Path.Homotopic.Quotient x y) (hx : x' = x) (hy : y' = y)
    (e : p ⁻¹' {x'}) :
    (hp.monodromy (γ.cast hx hy) e).1 =
      (hp.monodromy γ ⟨e, e.2.trans hx⟩).1 := by
  subst x'
  subst y'
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Lifting paths commutes with a morphism of covering spaces. -/
theorem monodromy_naturality
    {E F X Y : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [TopologicalSpace X] [TopologicalSpace Y]
    {p : E → X} {q : F → Y} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (L : C(E, F)) (g : C(X, Y))
    (hcomm : (⟨q, hq.continuous⟩ : C(F, Y)).comp L =
      g.comp ⟨p, hp.continuous⟩)
    (e : E) (γ : Path.Homotopic.Quotient (p e) (p e)) :
    (hq.monodromy (γ.map g) ⟨L e, congrArg (fun k : C(E, Y) ↦ k e) hcomm⟩).1 =
      L (hp.monodromy γ ⟨e, rfl⟩) := by
  let Γ := hp.liftPathQuotient γ ⟨e, rfl⟩
  have hend : q (L (hp.monodromy γ ⟨e, rfl⟩)) = g (p e) := by
    have hh := congrArg (fun k : C(E, Y) ↦ k (hp.monodromy γ ⟨e, rfl⟩)) hcomm
    exact hh.trans (congrArg g (hp.monodromy γ ⟨e, rfl⟩).2)
  apply congrArg Subtype.val
    (hq.monodromy_eq_of_map_eq (ey := ⟨_, hend⟩) (Γ.map L) ?_)
  rw [← Path.Homotopic.Quotient.map_comp]
  refine (Γ.map_congr_cast hcomm).trans ?_
  rw [Path.Homotopic.Quotient.map_comp, hp.map_liftPathQuotient,
    Path.Homotopic.Quotient.map_cast, Path.Homotopic.Quotient.cast_cast]

end IsCoveringMap
