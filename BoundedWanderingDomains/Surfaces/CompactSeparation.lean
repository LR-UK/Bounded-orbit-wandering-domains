/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Compactness.Compact

/-! # Separation by a compact set

The condition says that no component outside a compact set meets both sets.
Disjointness of the original sets is a separate hypothesis in the analytic
application. Either set being compact supplies this condition immediately.
No construction of an end compactification is needed.
-/

open Set

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X]

def SeparatedByCompact (K L : Set X) : Prop :=
  ∃ B : Set X, IsCompact B ∧ ∀ x : X,
    Disjoint (connectedComponentIn Bᶜ x) K ∨ Disjoint (connectedComponentIn Bᶜ x) L

theorem SeparatedByCompact.symm {K L : Set X} (h : SeparatedByCompact K L) :
    SeparatedByCompact L K := by
  obtain ⟨B, hB, hsep⟩ := h
  exact ⟨B, hB, fun x => (hsep x).symm⟩

theorem separatedByCompact_of_isCompact_left {K L : Set X} (hK : IsCompact K) :
    SeparatedByCompact K L := by
  refine ⟨K, hK, fun x => Or.inl ?_⟩
  exact disjoint_left.mpr (fun y hy hKy => (connectedComponentIn_subset Kᶜ x hy) hKy)

theorem separatedByCompact_of_isCompact_right {K L : Set X} (hL : IsCompact L) :
    SeparatedByCompact K L :=
  (separatedByCompact_of_isCompact_left hL).symm

theorem SeparatedByCompact.mono {K L K' L' : Set X}
    (h : SeparatedByCompact K L) (hK : K' ⊆ K) (hL : L' ⊆ L) :
    SeparatedByCompact K' L' := by
  obtain ⟨B, hB, hsep⟩ := h
  exact ⟨B, hB, fun x => (hsep x).imp (fun hk => hk.mono_right hK)
    (fun hl => hl.mono_right hL)⟩

/-- Any connected region avoiding the separator meets at most one of the sets. -/
theorem connected_region_misses_one_side {K L B C : Set X}
    (hsep : ∀ x : X, Disjoint (connectedComponentIn Bᶜ x) K ∨
      Disjoint (connectedComponentIn Bᶜ x) L)
    (hC : IsConnected C) (hCB : C ⊆ Bᶜ) : Disjoint C K ∨ Disjoint C L := by
  obtain ⟨x, hx⟩ := hC.nonempty
  have hsub : C ⊆ connectedComponentIn Bᶜ x :=
    hC.isPreconnected.subset_connectedComponentIn hx hCB
  exact (hsep x).imp (fun h => h.mono_left hsub) (fun h => h.mono_left hsub)

end AreaDeficit.Surfaces
