/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Logic.Function.Iterate

/-! # Filling relatively compact complementary components

This is the topological part of Baker filling, stated for surfaces without
choosing a global plane coordinate. All compactness is topological.
-/

open Set Function Filter Topology

namespace AreaDeficit.Surfaces

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def compactFill (K : Set X) : Set X :=
  {x | IsCompact (closure (connectedComponentIn Kᶜ x))}

theorem subset_compactFill (K : Set X) : K ⊆ compactFill K := by
  intro x hx
  change IsCompact (closure (connectedComponentIn Kᶜ x))
  rw [connectedComponentIn_eq_empty (show x ∉ Kᶜ from fun h => h hx), closure_empty]
  exact isCompact_empty

theorem compactFill_mono [T2Space X] {K L : Set X} (hKL : K ⊆ L) :
    compactFill K ⊆ compactFill L := by
  intro x hx
  exact hx.of_isClosed_subset isClosed_closure
    (closure_mono (connectedComponentIn_mono x (compl_subset_compl.mpr hKL)))

theorem isClosed_compactFill [LocallyConnectedSpace X] {K : Set X} (hK : IsClosed K) :
    IsClosed (compactFill K) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hxK : x ∉ K := fun h => hx (subset_compactFill K h)
  apply mem_of_superset (hK.isOpen_compl.connectedComponentIn.mem_nhds
    (mem_connectedComponentIn hxK))
  intro y hy hyfill
  apply hx
  change IsCompact (closure (connectedComponentIn Kᶜ x))
  change IsCompact (closure (connectedComponentIn Kᶜ y)) at hyfill
  rwa [← connectedComponentIn_eq hy] at hyfill

theorem frontier_component_subset_complement [LocallyConnectedSpace X]
    {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U) :
    frontier (connectedComponentIn U x) ⊆ Uᶜ := by
  intro y hy hyU
  have hy' : (⟨y, hyU⟩ : U) ∈ closure (connectedComponent (⟨x, hx⟩ : U)) := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    simpa only [Set.mem_preimage, connectedComponentIn_eq_image hx] using hy.1
  rw [isClosed_connectedComponent.closure_eq] at hy'
  have hyc : y ∈ connectedComponentIn U x := by
    rw [connectedComponentIn_eq_image hx]
    exact ⟨⟨y, hyU⟩, hy', rfl⟩
  exact hy.2 (hU.connectedComponentIn.interior_eq.symm ▸ hyc)

/-- A connected set avoiding the frontier cannot leave an open set it meets. -/
theorem preconnected_subset_open_of_avoids_frontier
    {C V : Set X} (hC : IsPreconnected C) (hV : IsOpen V)
    (havoid : Disjoint C (frontier V)) (hmeet : (C ∩ V).Nonempty) : C ⊆ V := by
  apply hC.subset_left_of_subset_union hV isClosed_closure.isOpen_compl
    (Set.disjoint_left.mpr (fun _ hx hy => hy (subset_closure hx))) _ hmeet
  intro x hx
  by_cases hxV : x ∈ V
  · exact Or.inl hxV
  · refine Or.inr (fun hxcl => ?_)
    apply Set.disjoint_left.mp havoid hx
    rw [frontier, hV.interior_eq]
    exact ⟨hxcl, hxV⟩

/-- Filling stays inside any compact set with connected exterior on a
noncompact ambient surface. -/
theorem compactFill_subset_compact_of_connected_complement
    [T2Space X] [NoncompactSpace X] {K L : Set X}
    (hKL : K ⊆ L) (hL : IsCompact L) (hLc : IsPreconnected Lᶜ) :
    compactFill K ⊆ L := by
  intro x hx
  by_contra hxL
  have hsub : Lᶜ ⊆ connectedComponentIn Kᶜ x :=
    hLc.subset_connectedComponentIn hxL (compl_subset_compl.mpr hKL)
  have hcl : IsCompact (closure Lᶜ) :=
    hx.of_isClosed_subset isClosed_closure (closure_mono hsub)
  have huniv : L ∪ closure Lᶜ = Set.univ := by
    apply eq_univ_of_univ_subset
    intro y _
    by_cases hy : y ∈ L
    · exact Or.inl hy
    · exact Or.inr (subset_closure hy)
  exact noncompact_univ X (by simpa only [huniv] using hL.union hcl)

theorem isCompact_compactFill_of_subset_compact
    [T2Space X] [LocallyConnectedSpace X] [NoncompactSpace X]
    {K L : Set X} (hK : IsClosed K) (hKL : K ⊆ L)
    (hL : IsCompact L) (hLc : IsPreconnected Lᶜ) :
    IsCompact (compactFill K) :=
  hL.of_isClosed_subset (isClosed_compactFill hK)
    (compactFill_subset_compact_of_connected_complement hKL hL hLc)

theorem isConnected_compactFill [ConnectedSpace X] [LocallyConnectedSpace X]
    {K : Set X} (hK : IsClosed K) (hconn : IsConnected K) :
    IsConnected (compactFill K) := by
  obtain ⟨a, ha⟩ := hconn.nonempty
  refine ⟨⟨a, subset_compactFill K ha⟩, isPreconnected_of_forall a ?_⟩
  intro x hx
  by_cases hxK : x ∈ K
  · exact ⟨K, subset_compactFill K, ha, hxK, hconn.isPreconnected⟩
  let C := connectedComponentIn Kᶜ x
  have hxC : x ∈ C := mem_connectedComponentIn hxK
  have hCc : IsConnected C := isConnected_connectedComponentIn_iff.mpr hxK
  have hCne : C ≠ Set.univ := by
    intro he
    have haC : a ∈ C := he.symm ▸ mem_univ a
    exact connectedComponentIn_subset Kᶜ x haC ha
  obtain ⟨b, hb⟩ := nonempty_frontier_iff.mpr ⟨⟨x, hxC⟩, hCne⟩
  have hbK : b ∈ K := by
    simpa only [compl_compl] using
      frontier_component_subset_complement hK.isOpen_compl hxK hb
  have hCfill : C ⊆ compactFill K := by
    intro y hy
    change IsCompact (closure (connectedComponentIn Kᶜ y))
    rw [← connectedComponentIn_eq hy]
    exact hx
  have hclfill : closure C ⊆ compactFill K :=
    closure_minimal hCfill (isClosed_compactFill hK)
  exact ⟨K ∪ closure C, union_subset (subset_compactFill K) hclfill,
    Or.inl ha, Or.inr (subset_closure hxC),
    (hconn.union ⟨b, hbK, hb.1⟩ hCc.closure).isPreconnected⟩

/-- The filling inclusion for a continuous open map is purely topological;
source and target may be different surfaces or a coordinate plane. -/
theorem image_compactFill_subset_compactFill_image_local
    [T2Space X] [T2Space Y] [LocallyConnectedSpace X]
    {g : X → Y} {K V : Set X} (hK : IsClosed K)
    (hKV : compactFill K ⊆ V) (hg : ContinuousOn g V)
    (hgo : ∀ D : Set X, D ⊆ V → IsOpen D → IsOpen (g '' D)) :
    g '' compactFill K ⊆ compactFill (g '' K) := by
  rintro _ ⟨x, hx, rfl⟩
  by_cases hxK : x ∈ K
  · exact subset_compactFill _ (mem_image_of_mem g hxK)
  let D := connectedComponentIn Kᶜ x
  have hDo : IsOpen D := hK.isOpen_compl.connectedComponentIn
  have hxD : x ∈ D := mem_connectedComponentIn hxK
  have hDF : D ⊆ compactFill K := by
    intro y hy
    change IsCompact (closure (connectedComponentIn Kᶜ y))
    rw [← connectedComponentIn_eq hy]
    exact hx
  have hclV : closure D ⊆ V :=
    (closure_minimal hDF (isClosed_compactFill hK)).trans hKV
  have hfront : frontier D ⊆ K := by
    simpa only [compl_compl] using
      frontier_component_subset_complement hK.isOpen_compl hxK
  have hIo : IsOpen (g '' D) := hgo D (hDF.trans hKV) hDo
  have hIc : IsCompact (g '' closure D) := hx.image_of_continuousOn (hg.mono hclV)
  have hIf : frontier (g '' D) ⊆ g '' K := by
    intro y hy
    have hycl : y ∈ g '' closure D :=
      closure_minimal (image_mono subset_closure) hIc.isClosed hy.1
    obtain ⟨v, hv, rfl⟩ := hycl
    refine mem_image_of_mem g (hfront ⟨hv, ?_⟩)
    intro hvi
    exact hy.2 (hIo.interior_eq.symm ▸ mem_image_of_mem g (interior_subset hvi))
  by_cases hgxK : g x ∈ g '' K
  · exact subset_compactFill _ hgxK
  let C := connectedComponentIn (g '' K)ᶜ (g x)
  have hCI : C ⊆ g '' D :=
    preconnected_subset_open_of_avoids_frontier isPreconnected_connectedComponentIn hIo
      (Set.disjoint_left.mpr (fun _ hy hyf =>
        connectedComponentIn_subset _ _ hy (hIf hyf)))
      ⟨g x, mem_connectedComponentIn hgxK, mem_image_of_mem g hxD⟩
  exact hIc.of_isClosed_subset isClosed_closure
    (closure_minimal (hCI.trans (image_mono subset_closure)) hIc.isClosed)

theorem compactFill_subset_interior_of_subset
    [LocallyConnectedSpace X] {K F : Set X} (hK : IsClosed K)
    (hKI : K ⊆ interior F) (hfill : compactFill K ⊆ F) :
    compactFill K ⊆ interior F := by
  intro x hx
  by_cases hxK : x ∈ K
  · exact hKI hxK
  have hCo := hK.isOpen_compl.connectedComponentIn (x := x)
  apply (hCo.subset_interior_iff.mpr (show connectedComponentIn Kᶜ x ⊆ F from ?_))
    (mem_connectedComponentIn hxK)
  intro y hy
  apply hfill
  change IsCompact (closure (connectedComponentIn Kᶜ y))
  rw [← connectedComponentIn_eq hy]
  exact hx

/-- Filled forward continua remain trapped as soon as their fillings stay
in the source of the continuous open map. -/
theorem compactFill_iterates_mem_of_forward
    [T2Space X] [LocallyConnectedSpace X]
    {f : X → X} {V : Set X}
    (hf : ContinuousOn f V)
    (hfo : ∀ D : Set X, D ⊆ V → IsOpen D → IsOpen (f '' D))
    {K : ℕ → Set X} (hK : ∀ n, IsClosed (K n))
    (hKV : ∀ n, compactFill (K n) ⊆ V)
    (hnext : ∀ n, MapsTo f (K n) (K (n + 1))) :
    ∀ n x, x ∈ compactFill (K n) → ∀ k : ℕ, (f^[k]) x ∈ V := by
  have hm : ∀ n, MapsTo f (compactFill (K n)) (compactFill (K (n + 1))) := by
    intro n
    apply mapsTo_iff_image_subset.mpr
    exact (image_compactFill_subset_compactFill_image_local (hK n) (hKV n) hf hfo).trans
      (compactFill_mono (hnext n).image_subset)
  intro n x hx k
  apply hKV (n + k)
  induction k with
  | zero => simpa using hx
  | succ k ih =>
      simpa only [Nat.add_succ, Function.iterate_succ_apply'] using hm (n + k) ih

end AreaDeficit.Surfaces

#print axioms AreaDeficit.Surfaces.image_compactFill_subset_compactFill_image_local
