module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.Surfaces.CompactSeparation
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Separation.Regular

@[expose] public section

/-! # Smooth cutoffs for compactly separated closed sets

A compact separator is converted to a smooth function which is zero near
one closed set and one near the other, and locally constant outside a
compact set. Neither closed set is assumed compact.
-/

open Set Filter Function
open scoped Topology Manifold ContDiff

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyConnectedSpace X]

/-- Partition the complement of the separator by whole connected components. -/
theorem exists_open_partition_of_compact_separator {K L B : Set X}
    (hB : IsCompact B)
    (hsep : ∀ x : X, Disjoint (connectedComponentIn Bᶜ x) K ∨
      Disjoint (connectedComponentIn Bᶜ x) L) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = Bᶜ ∧
      Disjoint U L ∧ Disjoint V K := by
  classical
  let C := fun x : X => connectedComponentIn Bᶜ x
  let U := ⋃ x, ⋃ (_h : Disjoint (C x) L), C x
  let V := ⋃ x, ⋃ (_h : ¬ Disjoint (C x) L), C x
  have ho (x : X) : IsOpen (C x) := hB.isClosed.isOpen_compl.connectedComponentIn
  have huv : Disjoint U V := by
    apply disjoint_left.mpr
    intro y hyU hyV
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hyU
    obtain ⟨w, hw, hyw⟩ := mem_iUnion₂.mp hyV
    have he : C x = C w :=
      (connectedComponentIn_eq hyx).trans (connectedComponentIn_eq hyw).symm
    exact hw (he ▸ hx)
  have hcover : U ∪ V = Bᶜ := by
    ext y
    constructor
    · intro hy
      rcases hy with hy | hy <;>
        obtain ⟨x, _, hx⟩ := mem_iUnion₂.mp hy <;>
        exact connectedComponentIn_subset Bᶜ x hx
    · intro hy
      by_cases h : Disjoint (C y) L
      · exact Or.inl (mem_iUnion₂.mpr ⟨y,h,mem_connectedComponentIn hy⟩)
      · exact Or.inr (mem_iUnion₂.mpr ⟨y,h,mem_connectedComponentIn hy⟩)
  refine ⟨U,V,isOpen_iUnion (fun x => isOpen_iUnion (fun _ => ho x)),
    isOpen_iUnion (fun x => isOpen_iUnion (fun _ => ho x)),huv,hcover,?_,?_⟩
  · apply disjoint_left.mpr
    intro y hy hL
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hy
    exact disjoint_left.mp hx hyx hL
  · apply disjoint_left.mpr
    intro y hy hK
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hy
    exact disjoint_left.mp ((hsep x).resolve_right hx) hyx hK

/-- Closed disjoint enlarged sides cover the complement of a compact set. -/
theorem exists_closed_sides [LocallyCompactSpace X]
    {K L : Set X} (hK : IsClosed K) (hL : IsClosed L) (hd : Disjoint K L)
    (hsep : SeparatedByCompact K L) :
    ∃ D A Z : Set X, IsCompact D ∧ IsClosed A ∧ IsClosed Z ∧
      Disjoint A Z ∧ K ⊆ A ∧ L ⊆ Z ∧ Dᶜ ⊆ A ∪ Z := by
  obtain ⟨B,hB,hsep⟩ := hsep
  obtain ⟨U,V,hU,hV,hUV,hcover,hUL,hVK⟩ :=
    exists_open_partition_of_compact_separator hB hsep
  obtain ⟨D,hD,_,hBD,_⟩ := exists_compact_closed_between hB isOpen_univ (subset_univ B)
  have hcUV : Disjoint (closure U) V :=
    disjoint_left.mpr (closure_minimal (disjoint_left.mp hUV) hV.isClosed_compl)
  have hcVU : Disjoint (closure V) U :=
    disjoint_left.mpr (closure_minimal (disjoint_left.mp hUV.symm) hU.isClosed_compl)
  have hout {x : X} (hx : x ∉ interior D) : x ∈ U ∪ V := by
    rw [hcover]
    exact fun h => hx (hBD h)
  let A := K ∪ (closure U ∩ (interior D)ᶜ)
  let Z := L ∪ (closure V ∩ (interior D)ᶜ)
  refine ⟨D,A,Z,hD,hK.union (isClosed_closure.inter isOpen_interior.isClosed_compl),
    hL.union (isClosed_closure.inter isOpen_interior.isClosed_compl),?_,
    subset_union_left,subset_union_left,?_⟩
  · apply disjoint_left.mpr
    intro x hxA hxZ
    rcases hxA with hxK | ⟨hxU,hxD⟩ <;> rcases hxZ with hxL | ⟨hxV,hxD'⟩
    · exact disjoint_left.mp hd hxK hxL
    · rcases hout hxD' with hx | hx
      · exact disjoint_left.mp hcVU hxV hx
      · exact disjoint_left.mp hVK hx hxK
    · rcases hout hxD with hx | hx
      · exact disjoint_left.mp hUL hx hxL
      · exact disjoint_left.mp hcUV hxU hx
    · rcases hout hxD with hx | hx
      · exact disjoint_left.mp hcVU hxV hx
      · exact disjoint_left.mp hcUV hxU hx
  · intro x hx
    have hi : x ∉ interior D := fun h => hx (interior_subset h)
    rcases hout hi with h | h
    · exact Or.inl (Or.inr ⟨subset_closure h,hi⟩)
    · exact Or.inr (Or.inr ⟨subset_closure h,hi⟩)

section Smooth
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [LocallyCompactSpace M] [LocallyConnectedSpace M]

/-- A smooth separating cutoff whose variation is confined to a compact set. -/
theorem exists_smooth_separating_cutoff {K L : Set M}
    (hK : IsClosed K) (hL : IsClosed L) (hd : Disjoint K L)
    (hsep : SeparatedByCompact K L) :
    ∃ D : Set M, IsCompact D ∧ ∃ χ : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯,
      (∀ᶠ x in 𝓝ˢ K, χ x = 0) ∧ (∀ᶠ x in 𝓝ˢ L, χ x = 1) ∧
      (∀ x, χ x ∈ Icc 0 1) ∧
      ∀ x ∉ D, (∀ᶠ y in 𝓝 x, χ y = 0) ∨ (∀ᶠ y in 𝓝 x, χ y = 1) := by
  obtain ⟨D,A,Z,hD,hA,hZ,hAZ,hKA,hLZ,hcover⟩ := exists_closed_sides hK hL hd hsep
  obtain ⟨χ,hχA,hχZ,hχ⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed I hA hZ hAZ
  refine ⟨D,hD,χ,?_,?_,hχ,?_⟩
  · exact hχA.filter_mono (nhdsSet_mono hKA)
  · exact hχZ.filter_mono (nhdsSet_mono hLZ)
  · intro x hx
    rcases hcover hx with ha | hz
    · exact Or.inl (hχA.filter_mono (nhds_le_nhdsSet ha))
    · exact Or.inr (hχZ.filter_mono (nhds_le_nhdsSet hz))

/-- The differential of the separating cutoff vanishes outside a compact set. -/
theorem exists_smooth_separating_cutoff_mfderiv {K L : Set M}
    (hK : IsClosed K) (hL : IsClosed L) (hd : Disjoint K L)
    (hsep : SeparatedByCompact K L) :
    ∃ D : Set M, IsCompact D ∧ ∃ χ : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯,
      (∀ᶠ x in 𝓝ˢ K, χ x = 0) ∧ (∀ᶠ x in 𝓝ˢ L, χ x = 1) ∧
      (∀ x, χ x ∈ Icc 0 1) ∧ ∀ x ∉ D, mfderiv I 𝓘(ℝ) χ x = 0 := by
  obtain ⟨D,hD,χ,hKχ,hLχ,hχ,hout⟩ := exists_smooth_separating_cutoff I hK hL hd hsep
  refine ⟨D,hD,χ,hKχ,hLχ,hχ,?_⟩
  intro x hx
  rcases hout x hx with h | h
  · simpa using Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ)) h
  · simpa using Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ)) h

end Smooth
end AreaDeficit.Surfaces
