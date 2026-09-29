module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.FinitePunctureTopology

@[expose] public section

/-! # Finite puncture stages inside a fixed anchor complement -/

open Set TopologicalSpace
open scoped Topology

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- The fixed open complement of a finite anchor set. -/
def anchorComplement (E : Finset X) : Opens X :=
  ⟨((↑E : Set X)ᶜ), E.finite_toSet.isClosed.isOpen_compl⟩

/-- Retain the points of a finite stage which lie in the fixed anchor
complement, now regarded as points of that open subsurface. -/
noncomputable def finiteStageOnAnchorComplement (E F : Finset X) :
    Finset (anchorComplement E) := by
  classical
  exact F.subtype (fun x => x ∈ anchorComplement E)

@[simp] theorem mem_finiteStageOnAnchorComplement
    (E F : Finset X) (x : anchorComplement E) :
    x ∈ finiteStageOnAnchorComplement E F ↔ (x : X) ∈ F := by
  classical
  simp [finiteStageOnAnchorComplement]

theorem finiteStageOnAnchorComplement_mono (E : Finset X) :
    Monotone (finiteStageOnAnchorComplement E) := by
  classical
  intro F G hFG
  exact Finset.subtype_mono hFG

/-- An increasing ambient sequence remains increasing after removing the
fixed anchors and passing to the anchor-complement subtype. -/
theorem finiteStageOnAnchorComplement_monotone (E : Finset X)
    {P : ℕ → Finset X} (hP : Monotone P) :
    Monotone (fun n => finiteStageOnAnchorComplement E (P n)) := by
  intro n m hnm
  exact finiteStageOnAnchorComplement_mono E (hP hnm)

/-- The points removed from the fixed anchor complement at a finite stage
are precisely the ambient stage points other than the anchors. -/
theorem coe_finiteStageOnAnchorComplement
    (E F : Finset X) :
    ((↑(finiteStageOnAnchorComplement E F) : Set (anchorComplement E))) =
      (Subtype.val : anchorComplement E → X) ⁻¹' (↑F : Set X) := by
  ext x
  simp

/-- Ambient density of finite stages transfers to density inside the fixed
anchor complement at every point which is not an anchor. -/
theorem mem_closure_iUnion_finiteStageOnAnchorComplement
    (E : Finset X) (P : ℕ → Finset X) (x : anchorComplement E)
    (hx : (x : X) ∈ closure (⋃ n, (↑(P n) : Set X))) :
    x ∈ closure (⋃ n,
      (↑(finiteStageOnAnchorComplement E (P n)) :
        Set (anchorComplement E))) := by
  rw [closure_subtype]
  apply mem_closure_iff.mpr
  intro V hV hxV
  have hO : IsOpen ((↑(anchorComplement E) : Set X)) :=
    (anchorComplement E).isOpen
  obtain ⟨y, hyVO, hyP⟩ :=
    mem_closure_iff.mp hx (V ∩ (anchorComplement E : Set X))
      (hV.inter hO) ⟨hxV, x.property⟩
  obtain ⟨n, hyn⟩ := mem_iUnion.mp hyP
  let yO : anchorComplement E := ⟨y, hyVO.2⟩
  refine ⟨y, hyVO.1, yO, ?_, rfl⟩
  exact mem_iUnion.mpr ⟨n,
    (mem_finiteStageOnAnchorComplement E (P n) yO).mpr hyn⟩

end AreaDeficit.Surfaces
