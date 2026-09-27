/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactGlobalAnchors
import BoundedWanderingDomains.Surfaces.CompactAnchorNormality
import BoundedWanderingDomains.Surfaces.CompactGlobalSingularValues
import BoundedWanderingDomains.Surfaces.CompactAnchorAreaReduction
import BoundedWanderingDomains.Surfaces.FiniteDefectAreaAdvance
import BoundedWanderingDomains.Surfaces.SubsurfaceRegularValues

/-! # Positive-area wandering sets for compact global surface maps -/

open Set Function MeasureTheory Topology
open AreaDeficit.Surfaces
open scoped Manifold Topology ContDiff ENNReal

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [CompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem false_of_compact_global_positive_area_wandering
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (hsource : f.source = ⊤)
    {A : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A) (hApos : HasPositiveChartArea A) : False := by
  classical
  obtain ⟨a, ha, b, hb, hba, c, hc, hca, hcb⟩ := hApos.exists_three
  letI : Nontrivial X := ⟨⟨a, b, Ne.symm hba⟩⟩
  letI : Infinite X := Set.infinite_univ_iff.mp
    ((infinite_of_mem_nhds (Classical.arbitrary X)
      ((chartAt ℂ (Classical.arbitrary X)).open_source.mem_nhds (mem_chart_source ℂ _))).mono
      (subset_univ _))
  letI : IsManifold 𝓘(ℂ) ω X := isManifold_analytic_of_complex
  obtain ⟨E, hEcard, hEA, P, hP, hEP, hPf, hPb, hPcover⟩ :=
    f.exists_three_anchor_backward_hyperbolic_models hf hsource hApos
  let O := anchorComplement E
  letI : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  let p : DiscCover O := Classical.choice
    (DiscCover.nonempty_compl_finset_of_card_three_subset E E hEcard (Subset.refl _))
  have hAP : A ⊆ closure (⋃ n, (P n : Set X)) := by
    intro x hx
    exact f.compl_omega_subset_closure_backward_anchors hf hsource E O (fun _ => Iff.rfl) p
      (fun y hy => mem_iUnion.mpr ⟨0, hEP 0 hy⟩) hPb (hAbad hx).2
  obtain ⟨B, hB⟩ := f.exists_finite_singularValues_of_compact_global hf hsource
  let J := B ∪ E.image f.totalize
  have hEJ : f.totalize '' (E : Set X) ⊆ (J : Set X) := by
    rintro y ⟨x, hx, rfl⟩
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
  let Vtop : TopologicalSpace.Opens X := ⊤
  have htopc : IsCompact (closure (Vtop : Set X)) := by simpa [Vtop] using (isCompact_univ : IsCompact (univ : Set X))
  have htops : closure (Vtop : Set X) ⊆ f.source := by simp [Vtop, hsource]
  obtain ⟨T, hT, hcontain, hback, hAstarm, hAstarpos, hAstarP, hAstarT⟩ :=
    f.exists_backwardExceptional_positive_remainder hf Vtop htopc htops P hP J hA hApos hAP
  let S := ⋃ n, (T n : Set X)
  let Astar := A \ S
  let W := f.saturation Astar
  have hScount : S.Countable := countable_iUnion (fun n => (T n).finite_toSet.countable)
  obtain ⟨_, hWm, hAW, _, hWinj, himage, hWdis⟩ :=
    f.diff_backwardExceptional_wandering_configuration_basic hf hA
      (fun x hx => (hAbad hx).1) hdis hinj (subset_univ _) (subset_univ _) hScount
      (fun x _ hx => hback x (by trivial) hx)
  have hES : (E : Set X) ⊆ S := fun x hx => mem_iUnion.mpr ⟨0, (hcontain 0).1 (hEP 0 hx)⟩
  have hJS : (J : Set X) ⊆ S := fun x hx => mem_iUnion.mpr ⟨0, (hcontain 0).2 hx⟩
  have hPS : ∀ n, (P n : Set X) ⊆ S := fun n x hx => mem_iUnion.mpr ⟨n, (hcontain n).1 hx⟩
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
  have hall : ∀ x : X, x ∈ f.source := by intro x; rw [hsource]; trivial
  let WO : Set O := Subtype.val ⁻¹' W
  let AO : Set O := Subtype.val ⁻¹' Astar
  let Q : ℕ → Finset O := fun n => finiteStageOnAnchorComplement E (P n)
  let R : Finset O := finiteStageOnAnchorComplement E J
  have hWs : WO ⊆ g.source := by
    intro x hx
    apply hfull ⟨x, hall x⟩ x.property
    rw [← f.totalize_eq (hall x)]
    exact hWO (hfW hx)
  have hval : ∀ x ∈ WO, (g.totalize x : X) = f.totalize (x : X) := by
    intro x hx
    rw [g.totalize_eq (hWs hx), f.totalize_eq (hall x)]
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
      rw [f.totalize_eq (hall _)]; rfl
    rcases hPf n ((x : O) : X) hxP with hh | hh
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

#print axioms SurfaceDynamics.false_of_compact_global_positive_area_wandering
