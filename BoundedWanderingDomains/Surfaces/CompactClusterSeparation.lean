/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.Statements
import Mathlib.Topology.Separation.Regular

/-! # Singular values near a compact cluster set -/

open Set Function Filter Topology

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [FirstCountableTopology X]

theorem compact_inter_finite_of_avoids_derived {S K : Set X}
    (hK : IsCompact K) (havoid : Disjoint K (derivedSet S)) : (S ∩ K).Finite := by
  by_contra hfin
  have hi : (S ∩ K).Infinite := hfin
  obtain ⟨x, hxK, hxacc⟩ := hi.exists_accPt_of_subset_isCompact
    hK inter_subset_right
  exact disjoint_left.mp havoid hxK (hxacc.mono (principal_mono.mpr inter_subset_left))

theorem eventually_mem_of_compact_cluster_subset
    (u : ℕ → X) {K O : Set X} (hK : IsCompact K) (hu : ∀ n, u n ∈ K)
    (hO : IsOpen O) (hcluster : ∀ x, MapClusterPt x atTop u → x ∈ O) :
    ∀ᶠ n in atTop, u n ∈ O := by
  by_contra hevent
  have hfreq : ∃ᶠ n in atTop, u n ∈ K ∩ Oᶜ := by
    exact (not_eventually.mp hevent).mono (fun n hn => ⟨hu n, hn⟩)
  obtain ⟨x, hx, hxc⟩ := (hK.inter_right hO.isClosed_compl).exists_mapClusterPt_of_frequently hfreq
  exact hx.2 (hcluster x hxc)

theorem exists_compact_cluster_singular_separation
    (u : ℕ → X) {K S : Set X} (hK : IsCompact K) (hu : ∀ n, u n ∈ K)
    (hS : IsClosed S)
    (hsep : ∀ x, MapClusterPt x atTop u → x ∉ derivedSet S) :
    ∃ (L0 L H : Set X) (E : Finset X),
      IsCompact L0 ∧ IsCompact L ∧ IsClosed H ∧ L0 ⊆ interior L ∧
      Disjoint L H ∧ S ⊆ H ∪ (E : Set X) ∧ (∀ᶠ n in atTop, u n ∈ L0) := by
  classical
  let C : Set X := {x | MapClusterPt x atTop u}
  have hCc : IsCompact C := hK.of_isClosed_subset isClosed_setOfPred_clusterPt
    (fun x hx => hK.isClosed.mem_of_mapClusterPt hx (Eventually.of_forall hu))
  obtain ⟨B, hBo, hCB, hBder, hBc⟩ := exists_open_between_and_isCompact_closure hCc
    (isClosed_derivedSet S).isOpen_compl (fun x hx => hsep x hx)
  have hEB : (S ∩ closure B).Finite := compact_inter_finite_of_avoids_derived hBc
    (disjoint_left.mpr (fun x hx hs => hBder hx hs))
  obtain ⟨V, hVo, hCV, hVB, hVc⟩ := exists_open_between_and_isCompact_closure hCc hBo hCB
  obtain ⟨Z, hZo, hCZ, hZV, hZc⟩ := exists_open_between_and_isCompact_closure hCc hVo hCV
  refine ⟨closure Z, closure V, S \ B, hEB.toFinset, hZc, hVc, hS.sdiff hBo,
    hZV.trans hVo.subset_interior_closure, ?_, ?_, ?_⟩
  · exact disjoint_left.mpr (fun x hx hxs => hxs.2 (hVB hx))
  · intro x hxS
    by_cases hxB : x ∈ B
    · exact Or.inr (hEB.mem_toFinset.mpr ⟨hxS, subset_closure hxB⟩)
    · exact Or.inl ⟨hxS, hxB⟩
  · exact (eventually_mem_of_compact_cluster_subset u hK hu hZo (fun x hx => hCZ hx)).mono
      (fun n hn => subset_closure hn)

end SurfaceDynamics

#print axioms SurfaceDynamics.exists_compact_cluster_singular_separation
