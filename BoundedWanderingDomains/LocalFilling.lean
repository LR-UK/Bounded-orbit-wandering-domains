module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.HolomorphicFilling
public import BoundedWanderingDomains.TrappedComponentCovering

@[expose] public section

/-! # Baker filling for a locally defined holomorphic map -/

open Set Metric Function Filter Bornology
open scoped Topology

namespace AreaDeficit

/-- Filling commutes with a continuous open map when it is defined on a
neighbourhood of the filled compactum. -/
theorem image_fill_subset_fill_image_local {g : ℂ → ℂ} {K V : Set ℂ}
    (hK : IsCompact K) (hKV : ComplexApproximation.fill K ⊆ V)
    (hg : ContinuousOn g V)
    (hgo : ∀ D : Set ℂ, D ⊆ V → IsOpen D → IsOpen (g '' D)) :
    g '' ComplexApproximation.fill K ⊆ ComplexApproximation.fill (g '' K) := by
  rintro _ ⟨z, hz, rfl⟩
  by_cases hzK : z ∈ K
  · exact ComplexApproximation.subset_fill _ (mem_image_of_mem g hzK)
  let D := connectedComponentIn Kᶜ z
  have hDo : IsOpen D := hK.isClosed.isOpen_compl.connectedComponentIn
  have hzD : z ∈ D := mem_connectedComponentIn hzK
  have hDb : IsBounded D := hz
  have hDF : D ⊆ ComplexApproximation.fill K := by
    intro w hw
    change IsBounded (connectedComponentIn Kᶜ w)
    exact (connectedComponentIn_eq hw) ▸ hz
  have hclV : closure D ⊆ V := (closure_minimal hDF
    (ComplexApproximation.isClosed_fill hK.isClosed)).trans hKV
  have hfront : frontier D ⊆ K := by
    simpa only [compl_compl] using
      ComplexApproximation.frontier_component_subset_compl hK.isClosed.isOpen_compl hzK
  have hIo : IsOpen (g '' D) := hgo D (hDF.trans hKV) hDo
  have hIc : IsCompact (g '' closure D) := hDb.isCompact_closure.image_of_continuousOn
    (hg.mono hclV)
  have hIf : frontier (g '' D) ⊆ g '' K := by
    intro w hw
    have hwcl : w ∈ g '' closure D :=
      closure_minimal (image_mono subset_closure) hIc.isClosed hw.1
    obtain ⟨v, hv, rfl⟩ := hwcl
    refine mem_image_of_mem g (hfront ⟨hv, ?_⟩)
    intro hvi
    exact hw.2 (hIo.interior_eq.symm ▸ mem_image_of_mem g (interior_subset hvi))
  by_contra hbad
  have hgK : g z ∉ g '' K := fun h => hbad (ComplexApproximation.subset_fill _ h)
  let C := connectedComponentIn (g '' K)ᶜ (g z)
  obtain ⟨w, hwC, hwf⟩ := ComplexApproximation.unbounded_connected_meets_frontier
    (C := C) isPreconnected_connectedComponentIn hbad hIo
    (hIc.isBounded.subset (image_mono subset_closure))
    ⟨g z, mem_connectedComponentIn hgK, mem_image_of_mem g hzD⟩
  exact connectedComponentIn_subset _ _ hwC (hIf hwf)

/-- If filled forward continua stay where the map is defined, all their
filled points are trapped. -/
theorem fill_subset_trapped_of_forward_fillings {f : ℂ → ℂ} {V : Set ℂ}
    (hf : ContinuousOn f V)
    (hfo : ∀ D : Set ℂ, D ⊆ V → IsOpen D → IsOpen (f '' D))
    {K : ℕ → Set ℂ} (hK : ∀ n, IsCompact (K n))
    (hKV : ∀ n, ComplexApproximation.fill (K n) ⊆ V)
    (hnext : ∀ n, MapsTo f (K n) (K (n+1))) :
    ∀ n, ComplexApproximation.fill (K n) ⊆ trappedSet f V := by
  have hm : ∀ n, MapsTo f (ComplexApproximation.fill (K n))
      (ComplexApproximation.fill (K (n+1))) := by
    intro n
    apply mapsTo_iff_image_subset.mpr
    exact (image_fill_subset_fill_image_local (hK n) (hKV n) hf hfo).trans
      (ComplexApproximation.fill_mono (hnext n).image_subset)
  intro n z hz k
  apply hKV (n+k)
  induction k with
  | zero => simpa using hz
  | succ k ih => simpa only [Nat.add_succ, iterate_succ_apply'] using hm (n+k) ih

/-- The filled holes are open; a compactum already in the trapped interior
therefore stays in that interior after filling. -/
theorem fill_subset_interior_of_fill_subset {K F : Set ℂ} (hK : IsClosed K)
    (hKI : K ⊆ interior F) (hfill : ComplexApproximation.fill K ⊆ F) :
    ComplexApproximation.fill K ⊆ interior F := by
  intro z hz
  by_cases hzK : z ∈ K
  · exact hKI hzK
  have hCo := hK.isOpen_compl.connectedComponentIn (x := z)
  apply (hCo.subset_interior_iff.mpr (show connectedComponentIn Kᶜ z ⊆ F from ?_))
    (mem_connectedComponentIn hzK)
  intro w hw
  apply hfill
  change IsBounded (connectedComponentIn Kᶜ w)
  exact (connectedComponentIn_eq hw) ▸ hz

end AreaDeficit
