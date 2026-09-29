module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.SimplyConnectedFilling
public import Mathlib.Analysis.Complex.AbsMax

@[expose] public section

/-! # Images and maximum-modulus bounds on filled compact sets -/

open Set Metric Bornology

namespace AreaDeficit

/-- A continuous open plane map takes a filled compact set into the filling
of its image. In particular this holds for nonconstant entire maps. -/
theorem image_fill_subset_fill_image {g : ℂ → ℂ} (hg : Continuous g)
    (hgo : IsOpenMap g) {K : Set ℂ} (hK : IsCompact K) :
    g '' ComplexApproximation.fill K ⊆ ComplexApproximation.fill (g '' K) := by
  rintro _ ⟨z, hz, rfl⟩
  by_cases hzK : z ∈ K
  · exact ComplexApproximation.subset_fill _ (mem_image_of_mem g hzK)
  let D := connectedComponentIn Kᶜ z
  have hDo : IsOpen D := hK.isClosed.isOpen_compl.connectedComponentIn
  have hzD : z ∈ D := mem_connectedComponentIn hzK
  have hDb : IsBounded D := hz
  have hfront : frontier D ⊆ K := by
    simpa only [compl_compl] using
      ComplexApproximation.frontier_component_subset_compl hK.isClosed.isOpen_compl hzK
  have hIc : IsCompact (g '' closure D) := hDb.isCompact_closure.image hg
  have hIf : frontier (g '' D) ⊆ g '' K := by
    intro w hw
    have hwcl : w ∈ g '' closure D :=
      closure_minimal (image_mono subset_closure) hIc.isClosed hw.1
    obtain ⟨v, hv, rfl⟩ := hwcl
    refine mem_image_of_mem g (hfront ⟨hv, ?_⟩)
    intro hvi
    exact hw.2 ((hgo D hDo).interior_eq.symm ▸ mem_image_of_mem g (interior_subset hvi))
  by_contra hbad
  have hgK : g z ∉ g '' K := fun h => hbad (ComplexApproximation.subset_fill _ h)
  let C := connectedComponentIn (g '' K)ᶜ (g z)
  obtain ⟨w, hwC, hwf⟩ := ComplexApproximation.unbounded_connected_meets_frontier
    (C := C) isPreconnected_connectedComponentIn hbad (hgo D hDo)
    (hIc.isBounded.subset (image_mono subset_closure))
    ⟨g z, mem_connectedComponentIn hgK, mem_image_of_mem g hzD⟩
  exact connectedComponentIn_subset _ _ hwC (hIf hwf)

/-- The maximum-modulus estimate on the boundary compactum extends to its
whole filling. -/
theorem norm_le_on_fill {g : ℂ → ℂ} {K : Set ℂ} {M : ℝ}
    (hK : IsCompact K) (hg : Differentiable ℂ g)
    (hb : ∀ z ∈ K, ‖g z‖ ≤ M) :
    ∀ z ∈ ComplexApproximation.fill K, ‖g z‖ ≤ M := by
  intro z hz
  by_cases hzK : z ∈ K
  · exact hb z hzK
  have hfront : frontier (connectedComponentIn Kᶜ z) ⊆ K := by
    simpa only [compl_compl] using
      ComplexApproximation.frontier_component_subset_compl hK.isClosed.isOpen_compl hzK
  change IsBounded (connectedComponentIn Kᶜ z) at hz
  exact Complex.norm_le_of_forall_mem_frontier_norm_le hz hg.diffContOnCl
    (fun w hw => hb w (hfront hw)) (subset_closure (mem_connectedComponentIn hzK))

end AreaDeficit
