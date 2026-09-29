module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.RegularCoveringArea
public import BoundedWanderingDomains.Surfaces.PositiveAreaAdvanceReduction
public import BoundedWanderingDomains.Surfaces.PositiveAreaExceptionalReduction
public import BoundedWanderingDomains.Surfaces.ForwardSourceBarrier
public import BoundedWanderingDomains.Surfaces.BarrierCompactOrbit
public import BoundedWanderingDomains.Surfaces.CompactClusterSeparation
public import BoundedWanderingDomains.Surfaces.OmegaDynamics
public import BoundedWanderingDomains.Surfaces.CompactAnchorNormality
public import BoundedWanderingDomains.Surfaces.AnchorComplementModels
public import BoundedWanderingDomains.Surfaces.CompactGlobalAnchors
public import BoundedWanderingDomains.Surfaces.CompactGlobalSingularValues
public import BoundedWanderingDomains.Surfaces.CompactAnchorAreaReduction
public import BoundedWanderingDomains.Surfaces.FiniteDefectAreaAdvance
public import BoundedWanderingDomains.Surfaces.SubsurfaceRegularValues

@[expose] public section

/-! # Area exclusion away from derived singular values -/

open Set Function Filter MeasureTheory
open AreaDeficit.Surfaces
open scoped Topology Manifold ENNReal

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]

theorem compact_singular_separation_of_disjoint_derived
    {K S : Set X} (hK : IsCompact K) (hS : IsClosed S)
    (havoid : Disjoint K (derivedSet S)) :
    ∃ (H : Set X) (E : Finset X), IsClosed H ∧ Disjoint K H ∧ S ⊆ H ∪ (E : Set X) := by
  classical
  obtain ⟨B, hBo, hKB, hBder, hBc⟩ := exists_open_between_and_isCompact_closure hK
    (isClosed_derivedSet S).isOpen_compl (fun x hx => disjoint_left.mp havoid hx)
  have hE : (S ∩ closure B).Finite := compact_inter_finite_of_avoids_derived hBc
    (disjoint_left.mpr (fun x hx hs => hBder hx hs))
  refine ⟨S \ B, hE.toFinset, hS.sdiff hBo,
    disjoint_left.mpr (fun x hx hs => hs.2 (hKB hx)), ?_⟩
  intro x hx
  by_cases hxB : x ∈ B
  · exact Or.inr (hE.mem_toFinset.mpr ⟨hx, subset_closure hxB⟩)
  · exact Or.inl ⟨hx, hxB⟩

variable [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [SecondCountableTopology X]

theorem LocalMap.exists_countable_backward_invariant_superset
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (P : ℕ → Finset X) (E : Finset X) :
    ∃ S : Set X, S.Countable ∧ (∀ n, (P n : Set X) ⊆ S) ∧
      (E : Set X) ⊆ S ∧ (∀ x : f.source, f.map x ∈ S → (x : X) ∈ S) := by
  classical
  let : LocallyCompactSpace f.source := f.source.isOpen.locallyCompactSpace
  let K : CompactExhaustion f.source := CompactExhaustion.choice f.source
  let Q : ℕ → Set X := fun n => (P n ∪ E : Finset X)
  let T := f.sourceExhaustiveBackwardTree K Q
  let S : Set X := ⋃ n, T n
  have hfin : ∀ n, (T n).Finite :=
    f.sourceExhaustiveBackwardTree_finite hf K.isCompact (fun n => (P n ∪ E).finite_toSet)
  refine ⟨S, countable_iUnion (fun n => (hfin n).countable), ?_, ?_, ?_⟩
  · intro n x hx
    exact mem_iUnion.mpr ⟨n, f.roots_subset_sourceExhaustiveBackwardTree n
      (Finset.mem_union_left E hx)⟩
  · intro x hx
    exact mem_iUnion.mpr ⟨0, f.roots_subset_sourceExhaustiveBackwardTree 0
      (Finset.mem_union_right (P 0) hx)⟩
  · exact f.sourceExhaustiveBackwardTree_union_backward (OrderHomClass.mono K) K.iUnion_eq

variable [MeasurableSpace X] [BorelSpace X]

theorem no_compact_positive_hyperbolic_area_saturation_of_singular_separation
    (p : DiscCover X) (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A K : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A) (hpos : 0 < p.hyperbolicArea A)
    (hK : IsCompact K) (H : Set X) (E : Finset X)
    (hH : IsClosed H) (hKH : Disjoint K H) (hSE : f.singularValues ⊆ H ∪ (E : Set X))
    (hsatK : f.saturation A ⊆ K) : False := by
  classical
  obtain ⟨P, hP, hfront, hPf, hPb, _⟩ :=
    f.exists_forward_source_finitePuncture_barrier hf f.isOpen_omega f.omega_subset_source
      (fun x hx => by
        have hh := f.totalize_mapsTo_omega hf hx
        rwa [f.totalize_eq (f.omega_subset_source hx)] at hh)
  have hAP : A ⊆ closure (⋃ n, (P n : Set X)) := by
    intro x hx
    by_contra hxP
    have hcomp := f.barrier_component_subset_omega_of_compact_orbit hf p
      isClosed_closure hfront hPb (hAbad hx).1 hxP hK
      (fun n => hsatK (mem_iUnion.mpr ⟨n, x, hx,
        f.iterate_eq_some_orbit n ⟨x, (hAbad hx).1⟩⟩))
    exact (hAbad hx).2 (hcomp (mem_connectedComponentIn hxP))
  obtain ⟨S, hScount, hPS, hES, hback⟩ :=
    f.exists_countable_backward_invariant_superset hf P E
  let Astar := A \ S
  let W := f.saturation Astar
  obtain ⟨hAstarm, hWm, hAW, hWK, hWinj, himage, hWS⟩ :=
    f.diff_backwardExceptional_wandering_configuration_basic hf hA
      (fun x hx => (hAbad hx).1) hdis hinj hsatK (subset_univ K) hScount
      (fun x _ hx => hback x hx)
  have hAstarpos : 0 < p.hyperbolicArea Astar := by
    rw [hyperbolicArea_diff_countable p A hScount]
    exact hpos
  have hAstarP : Astar ⊆ closure (⋃ n, (P n : Set X)) := sdiff_subset.trans hAP
  have hWs : W ⊆ f.source :=
    (f.saturation_subset_trapped (sdiff_subset.trans (fun x hx => (hAbad hx).1))).trans
      f.trapped_subset_source
  have hfW : f.totalize '' W ⊆ K := by
    rw [himage]
    exact sdiff_subset.trans hWK
  obtain ⟨C, hC, hstep⟩ := f.exists_uniform_singular_area_advance hf p E hH hK hKH hSE
  apply false_of_positive_hyperbolicArea_area_advances p P hP hAstarm hAstarpos hAstarP 0 hK hC
  intro n
  refine ⟨∅, f.totalize, W, by simp, hAW, hWK, ?_, ?_, ?_⟩
  · rw [himage]
    exact hWm.diff hAstarm
  · rw [himage]
  · simpa only [Finset.union_empty] using hstep (P n) (hPf n) W hWm hWs hWinj hfW (by
      intro x hx
      have hfWS : f.totalize x ∉ S := by
        apply disjoint_left.mp hWS
        have hh : f.totalize x ∈ f.totalize '' W := ⟨x, hx, rfl⟩
        rw [himage] at hh
        exact hh.1
      exact ⟨fun hp => hfWS (hPS n hp), fun he => hfWS (hES he)⟩)

theorem no_compact_positive_area_saturation_away_from_derived_of_discCover
    (p : DiscCover X) (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A K : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A) (hpos : HasPositiveChartArea A)
    (hK : IsCompact K) (havoid : Disjoint K (derivedSet f.singularValues))
    (hsatK : f.saturation A ⊆ K) : False := by
  obtain ⟨H, E, hH, hKH, hSE⟩ :=
    compact_singular_separation_of_disjoint_derived hK f.isClosed_singularValues havoid
  exact no_compact_positive_hyperbolic_area_saturation_of_singular_separation p f hf hA hAbad hdis hinj
    (hpos.hyperbolicArea_pos hA p)
    hK H E hH hKH hSE hsatK

end SurfaceDynamics

open Set Function Filter TopologicalSpace
open AreaDeficit.Surfaces
open SurfaceDynamics
open scoped Topology Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X]

theorem sourceExhaustiveBackwardTree_forward_defect
    (f : LocalMap X) (K : ℕ → Set f.source) (Q : ℕ → Set X) (J : Set X)
    (hQ : ∀ n (x : f.source), (x : X) ∈ Q n → f.map x ∈ J) (n : ℕ) :
    ∀ x : f.source, (x : X) ∈ f.sourceExhaustiveBackwardTree K Q n →
      f.map x ∈ f.sourceExhaustiveBackwardTree K Q n ∪ J := by
  induction n with
  | zero => exact fun x hx => Or.inr (hQ 0 x hx)
  | succ n ih =>
      intro x hx
      rcases hx with ((hx | hx) | ⟨y, hy, he⟩)
      · rcases ih x hx with hp | hj
        · exact Or.inl (Or.inl (Or.inl hp))
        · exact Or.inr hj
      · exact Or.inr (hQ (n + 1) x hx)
      · have hey : y = x := Subtype.ext he
        exact Or.inl (Or.inl (Or.inl (hey ▸ hy.2)))

variable [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

theorem exists_finite_source_anchor_models
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (E : Finset X) :
    ∃ P : ℕ → Finset X, Monotone P ∧ (∀ n, E ⊆ P n) ∧
      frontier (f.source : Set X) ⊆ closure (⋃ n, (P n : Set X)) ∧
      (∀ n (x : f.source), (x : X) ∈ P n →
        f.map x ∈ (P n : Set X) ∪ f.totalize '' (E : Set X)) ∧
      (∀ x : f.source, f.map x ∈ closure (⋃ n, (P n : Set X)) →
        (x : X) ∈ closure (⋃ n, (P n : Set X))) := by
  classical
  let : LocallyCompactSpace f.source := f.source.isOpen.locallyCompactSpace
  obtain ⟨Q₀, _, hQfront, hQcl⟩ := closed_set_dense_finite_exhaustion
    (isClosed_frontier : IsClosed (frontier (f.source : Set X)))
  let Q : ℕ → Set X := fun n => (Q₀ n ∪ E : Finset X)
  let K : CompactExhaustion f.source := CompactExhaustion.choice f.source
  let T := f.sourceExhaustiveBackwardTree K Q
  have hfin : ∀ n, (T n).Finite :=
    f.sourceExhaustiveBackwardTree_finite hf K.isCompact (fun n => (Q₀ n ∪ E).finite_toSet)
  let P : ℕ → Finset X := fun n => (hfin n).toFinset
  have hcoe : ∀ n, (P n : Set X) = T n := fun n => (hfin n).coe_toFinset
  have hQdef : ∀ n (x : f.source), (x : X) ∈ Q n → f.map x ∈ f.totalize '' (E : Set X) := by
    intro n x hx
    rcases Finset.mem_union.mp hx with hfront | he
    · exact ((disjoint_frontier_iff_isOpen.mpr f.source.isOpen).le_bot ⟨hQfront n hfront, x.property⟩).elim
    · exact ⟨x, he, f.totalize_eq x.property⟩
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · intro n m hnm x hx
    exact (hfin m).mem_toFinset.mpr (f.sourceExhaustiveBackwardTree_mono K Q hnm
      ((hfin n).mem_toFinset.mp hx))
  · intro n x hx
    exact (hfin n).mem_toFinset.mpr (f.roots_subset_sourceExhaustiveBackwardTree n
      (Finset.mem_union_right (Q₀ n) hx))
  · simp_rw [hcoe]
    rw [← hQcl]
    apply closure_mono
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n, f.roots_subset_sourceExhaustiveBackwardTree n
      (Finset.mem_union_left E hn)⟩
  · intro n x hx
    change (x : X) ∈ (P n : Set X) at hx
    rw [hcoe] at hx ⊢
    exact f.sourceExhaustiveBackwardTree_forward_defect K Q _ hQdef n x hx
  · simp_rw [hcoe]
    exact f.closure_source_backward_invariant hf.1
      (f.sourceExhaustiveBackwardTree_union_backward (OrderHomClass.mono K) K.iUnion_eq)

variable [CompactSpace X]

theorem bad_compact_source_points_subset_anchor_barrier
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (E : Finset X) (p : DiscCover (anchorComplement E))
    (P : ℕ → Finset X) (hEP : (E : Set X) ⊆ closure (⋃ n, (P n : Set X)))
    (hfront : frontier (f.source : Set X) ⊆ closure (⋃ n, (P n : Set X)))
    (hback : ∀ x : f.source, f.map x ∈ closure (⋃ n, (P n : Set X)) →
      (x : X) ∈ closure (⋃ n, (P n : Set X))) :
    f.trapped \ f.omega ⊆ closure (⋃ n, (P n : Set X)) := by
  intro x hx
  by_contra hxP
  let : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  let C := closure (⋃ n, (P n : Set X))
  let W := componentDomain ⟨Cᶜ, isClosed_closure.isOpen_compl⟩ x
  have hxW : x ∈ W := mem_componentDomain hxP
  have hWtr : (W : Set X) ⊆ f.trapped :=
    f.trapped_barrier_component hf.2.continuous isClosed_closure hfront hback hx.1 hxP
  have hWO : ∀ n y, f.orbitOn W hWtr n y ∈ anchorComplement E := by
    intro n y
    have hnot : ∀ k, f.orbit k ⟨y, hWtr y.property⟩ ∉ C := by
      intro k
      induction k with
      | zero => exact connectedComponentIn_subset _ _ y.property
      | succ k ih =>
          intro hh
          apply ih
          apply hback ⟨f.orbit k ⟨y, hWtr y.property⟩, f.orbit_mem_source k _⟩
          rwa [← f.orbit_succ k ⟨y, hWtr y.property⟩]
    exact fun he => hnot n (hEP he)
  exact hx.2 (f.mem_omega_of_omits_finite_anchors hf E (anchorComplement E) (fun _ => Iff.rfl)
    p W hWtr hWO ⟨x, hxW⟩)

end SurfaceDynamics.LocalMap


open Set Function MeasureTheory Topology
open AreaDeficit.Surfaces
open scoped Manifold Topology ContDiff ENNReal

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [CompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem false_of_compact_finite_singular_positive_area_wandering
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (hS : f.singularValues.Finite)
    {A : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A) (hApos : HasPositiveChartArea A) : False := by
  classical
  obtain ⟨a, ha, b, hb, hba, c, hc, hca, hcb⟩ := hApos.exists_three
  let : Nontrivial X := ⟨⟨a, b, Ne.symm hba⟩⟩
  let : Infinite X := Set.infinite_univ_iff.mp
    ((infinite_of_mem_nhds (Classical.arbitrary X)
      ((chartAt ℂ (Classical.arbitrary X)).open_source.mem_nhds (mem_chart_source ℂ _))).mono
      (subset_univ _))
  let : IsManifold 𝓘(ℂ) ω X := isManifold_analytic_of_complex
  let E : Finset X := {a, b, c}
  have hEcard : E.card = 3 := by
    simp [E, Ne.symm hba, Ne.symm hca, Ne.symm hcb]
  obtain ⟨P, hP, hEP, hfront, hPf, hPb⟩ := f.exists_finite_source_anchor_models hf E
  let O := anchorComplement E
  let : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  let p : DiscCover O := Classical.choice
    (DiscCover.nonempty_compl_finset_of_card_three_subset E E hEcard (Subset.refl _))
  have hAP : A ⊆ closure (⋃ n, (P n : Set X)) :=
    hAbad.trans (f.bad_compact_source_points_subset_anchor_barrier hf E p P
      (fun x hx => subset_closure (mem_iUnion.mpr ⟨0, hEP 0 hx⟩)) hfront hPb)
  let B := hS.toFinset
  have hB : f.singularValues ⊆ (B : Set X) := fun _ hx => hS.mem_toFinset.mpr hx
  let J := B ∪ E.image f.totalize
  have hEJ : f.totalize '' (E : Set X) ⊆ (J : Set X) := by
    rintro y ⟨x, hx, rfl⟩
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
  obtain ⟨S, hScount, hPS, hJS, hback⟩ :=
    f.exists_countable_backward_invariant_superset hf P J
  let Astar := A \ S
  let W := f.saturation Astar
  obtain ⟨hAstarm, hWm, hAW, _, hWinj, himage, hWdis⟩ :=
    f.diff_backwardExceptional_wandering_configuration_basic hf hA
      (fun x hx => (hAbad hx).1) hdis hinj (subset_univ _) (subset_univ _) hScount
      (fun x _ hx => hback x hx)
  have hAstarpos : HasPositiveChartArea Astar := hApos.diff_countable hScount
  have hAstarP : Astar ⊆ closure (⋃ n, (P n : Set X)) := sdiff_subset.trans hAP
  have hES : (E : Set X) ⊆ S := fun x hx => hPS 0 (hEP 0 hx)
  have hWsource : W ⊆ f.source :=
    (f.saturation_subset_trapped (sdiff_subset.trans (fun x hx => (hAbad hx).1))).trans
      f.trapped_subset_source
  have hWO : W ⊆ O := fun x hx he => disjoint_left.mp hWdis hx (hES he)
  have hfW : MapsTo f.totalize W W := by
    intro x hx
    have hh : f.totalize x ∈ f.totalize '' W := ⟨x, hx, rfl⟩
    rw [himage] at hh
    exact hh.1
  obtain ⟨V, hVs, hVO, hm, hfull⟩ := f.exists_full_restriction_to_open hf O
  let r := f.restrictSource V hVs
  let g := r.restrictAmbient O hVO hm
  have hr := f.isOpenHolomorphic_restrictSource hf V hVs
  have hg := r.isOpenHolomorphic_restrictAmbient hr O hVO hm
  let WO : Set O := Subtype.val ⁻¹' W
  let AO : Set O := Subtype.val ⁻¹' Astar
  let Q : ℕ → Finset O := fun n => finiteStageOnAnchorComplement E (P n)
  let R : Finset O := finiteStageOnAnchorComplement E J
  have hWs : WO ⊆ g.source := by
    intro x hx
    apply hfull ⟨x, hWsource hx⟩ x.property
    rw [← f.totalize_eq (hWsource hx)]
    exact hWO (hfW hx)
  have hval : ∀ x ∈ WO, (g.totalize x : X) = f.totalize (x : X) := by
    intro x hx
    rw [g.totalize_eq (hWs hx), f.totalize_eq (hWsource hx)]
    rfl
  have hWOm : MeasurableSet WO := hWm.preimage continuous_subtype_val.measurable
  have hAOm : MeasurableSet AO := hAstarm.preimage continuous_subtype_val.measurable
  have himageO : g.totalize '' WO = WO \ AO := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hh : f.totalize (x : X) ∈ W \ Astar := himage ▸ ⟨(x : X), hx, rfl⟩
      change (g.totalize x : X) ∈ W \ Astar
      rwa [hval x hx]
    · intro hy
      have hh : (y : X) ∈ f.totalize '' W := himage.symm ▸ hy
      obtain ⟨x, hx, hxy⟩ := hh
      let xo : O := ⟨x, hWO hx⟩
      refine ⟨xo, hx, Subtype.ext ?_⟩
      exact (hval xo hx).trans hxy
  have hginj : InjOn g.totalize WO := by
    intro x hx y hy he
    apply Subtype.ext
    apply hWinj hx hy
    have hh := congrArg Subtype.val he
    rwa [hval x hx, hval y hy] at hh
  have hsing : g.singularValues ⊆ (R : Set O) := by
    intro y hy
    have hh := f.singularValues_restrictAmbient_restrictSource_subset hf O V hVs hVO hm hfull
      J.finite_toSet.isClosed (fun x hx => hEJ ⟨x, not_not.mp hx, f.totalize_eq x.property⟩)
      ⟨y, hy, rfl⟩
    apply (mem_finiteStageOnAnchorComplement E J y).mpr
    rcases hh with hh | hh
    · exact Finset.mem_union.mpr (Or.inl (hB hh))
    · exact hh
  have hforward : ∀ n (x : g.source), (x : O) ∈ Q n → g.map x ∈ (Q n ∪ R : Finset O) := by
    intro n x hx
    have hxP : ((x : O) : X) ∈ P n := (mem_finiteStageOnAnchorComplement E (P n) (x : O)).mp hx
    have hv : (g.map x : X) = f.totalize ((x : O) : X) := by
      rw [f.totalize_eq (hVs x.property)]; rfl
    have hstep := hPf n ⟨((x : O) : X), hVs x.property⟩ hxP
    rw [← f.totalize_eq (hVs x.property)] at hstep
    rcases hstep with hh | hh
    · apply Finset.mem_union.mpr
      apply Or.inl
      apply (mem_finiteStageOnAnchorComplement E (P n) (g.map x)).mpr
      rwa [hv]
    · apply Finset.mem_union.mpr
      apply Or.inr
      apply (mem_finiteStageOnAnchorComplement E J (g.map x)).mpr
      rw [hv]
      exact hEJ hh
  have havoid : ∀ n x, x ∈ WO → g.totalize x ∉ (Q n ∪ R : Finset O) := by
    intro n x hx hh
    have hmemW := hfW hx
    apply disjoint_left.mp hWdis hmemW
    rcases Finset.mem_union.mp hh with hh | hh
    · have hm := (mem_finiteStageOnAnchorComplement E (P n) (g.totalize x)).mp hh
      rw [hval x hx] at hm
      exact hPS n hm
    · have hm := (mem_finiteStageOnAnchorComplement E J (g.totalize x)).mp hh
      rw [hval x hx] at hm
      exact hJS hm
  have hp := anchorComplement_globalFinitePunctureAreaPackage E p R.card
  apply false_of_anchorComplement_global_package E p R.card hp P hP hAstarm hAstarpos
    (disjoint_left.mpr (fun x hx he => hx.2 (hES he))) hAstarP (C := 0) (by simp)
  dsimp only
  intro n
  refine ⟨R, g.totalize, WO, le_rfl, (fun x hx => hAW hx), ?_, ?_, ?_⟩
  · rw [himageO]
    exact hWOm.diff hAOm
  · rw [himageO]
  · simpa only [add_zero] using g.finite_defect_domainArea_advance hg p (Q n) R hsing
      (hforward n) hWOm hWs hginj (havoid n)

end SurfaceDynamics
