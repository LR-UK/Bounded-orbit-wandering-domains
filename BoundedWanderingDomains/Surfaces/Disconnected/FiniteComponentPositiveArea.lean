module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.TargetAnchors
public import BoundedWanderingDomains.Surfaces.SingularEncounters.AnchorRegularPieces
public import BoundedWanderingDomains.Surfaces.SingularEncounters.CountableCrossAmbientArea
public import BoundedWanderingDomains.Surfaces.SingularEncounters.ControlledAreaCover
public import BoundedWanderingDomains.Surfaces.AlmostEverywhere.AreaBarrierModels
public import BoundedWanderingDomains.Surfaces.PositiveAreaExceptionalReduction
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseFiniteComplementArea
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseFiniteAreaPunctures
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseAreaBlowup
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwisePositiveArea
public import BoundedWanderingDomains.Surfaces.PositiveAreaOpenSubtype

@[expose] public section

/-! # Finite component control with finitely many ambient components -/

open Set Function Filter MeasureTheory Topology
open AreaDeficit.Surfaces
open scoped Manifold ContDiff ENNReal

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [Finite (ConnectedComponents X)] [MeasurableSpace X] [BorelSpace X]

theorem no_positive_area_finite_control_finitely_many_components
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A K : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A) (hpos : HasPositiveChartArea A)
    (hK : IsCompact K) (hsatK : f.saturation A ⊆ K)
    {ι : Type*} [Fintype ι] (D : ι → EmbeddedDisc X) (E : Finset X)
    (L : ι → Set X) (hL : ∀ i, IsCompact (L i)) (hLD : ∀ i, L i ⊆ (D i).carrier)
    (hcontrol : ∀ x ∈ f.saturation A, ∃ i, f.totalize x ∈ L i ∧
      x ∈ f.finiteObstructionSource hf.2.continuous (D i).carrier (E : Set X)) : False := by
  classical
  obtain ⟨a, ha⟩ := hpos.nonempty
  obtain ⟨i₀, _⟩ := hcontrol a (f.subset_saturation A ha)
  choose Fi hLFi hq using fun i => exists_componentwise_anchors_disjoint_compact_in_disc
    (D i) (hL i) (hLD i)
  let F : Finset X := Finset.univ.biUnion Fi
  have hFiF : ∀ i, Fi i ⊆ F := fun i => Finset.subset_biUnion_of_mem Fi (Finset.mem_univ i)
  let O := anchorComplement F
  let Oi : ι → TopologicalSpace.Opens X := fun i => anchorComplement (Fi i)
  let : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  let localCompactTargets : ∀ i, LocallyCompactSpace (Oi i) := fun i => (Oi i).isOpen.locallyCompactSpace
  let q : ∀ i, ComponentwiseDiscCover (Oi i) := fun i => Classical.choice (hq i)
  have hOOi : ∀ i, (O : Set X) ⊆ Oi i := fun i x hx hxi => hx (hFiF i hxi)
  let j : ∀ i, O → Oi i := fun i => Set.inclusion (hOOi i)
  have hj : ∀ i, IsOpenEmbedding (j i) := fun i =>
    .of_continuous_injective_isOpenMap (continuous_inclusion (hOOi i))
      (Set.inclusion_injective (hOOi i)) (O.isOpen.isOpenMap_inclusion (hOOi i))
  have hjh : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (j i) := by
    intro i
    apply (mdifferentiable_subtypeVal_comp_iff (Oi i) (j i)).mp
    exact mdifferentiable_subtype_val O
  let p : ComponentwiseDiscCover O := (q i₀).pullback (j i₀) (hjh i₀) (hj i₀).isLocalHomeomorph
  let Di : ∀ i, TopologicalSpace.Opens (Oi i) := fun i =>
    ⟨Subtype.val ⁻¹' ((D i).carrier : Set X), (D i).carrier.isOpen.preimage continuous_subtype_val⟩
  let Li : ∀ i, Set (Oi i) := fun i => Subtype.val ⁻¹' L i
  have hLic : ∀ i, IsCompact (Li i) := by
    intro i
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    convert hL i using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, disjoint_left.mp (hLFi i) hx⟩, hx, rfl⟩
  obtain ⟨P, hP, hEP, hfront, hPf, hPb⟩ := f.exists_finite_source_anchor_models hf F
  have hAP : A ⊆ closure (⋃ n, (P n : Set X)) := by
    intro x hx
    exact f.bad_compact_orbit_point_mem_anchor_barrier hf F p P
      (fun y hy => subset_closure (mem_iUnion.mpr ⟨0, hEP 0 hy⟩)) hfront hPb (hAbad hx) hK
      (fun n => hsatK (mem_iUnion.mpr ⟨n, x, hx, f.iterate_eq_some_orbit n ⟨x, (hAbad hx).1⟩⟩))
  let J := E ∪ F.image f.totalize
  have hEJ : (E : Set X) ⊆ (J : Set X) := Finset.subset_union_left
  have hFJ : f.totalize '' (F : Set X) ⊆ (J : Set X) := by
    rintro y ⟨x, hx, rfl⟩
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  obtain ⟨S, hScount, hPS, hJS, hback⟩ :=
    f.exists_countable_backward_invariant_superset hf P J
  let Astar := A \ S
  let W := f.saturation Astar
  obtain ⟨hAstarm, hWm, hAW, hWK, hWinj, himage, hWdis⟩ :=
    f.diff_backwardExceptional_wandering_configuration_basic hf hA
      (fun x hx => (hAbad hx).1) hdis hinj hsatK (subset_univ K) hScount
      (fun x _ hx => hback x hx)
  have hAstarpos : HasPositiveChartArea Astar := hpos.diff_countable hScount
  have hAstarP : Astar ⊆ closure (⋃ n, (P n : Set X)) := sdiff_subset.trans hAP
  have hFS : (F : Set X) ⊆ S := fun x hx => hPS 0 (hEP 0 hx)
  have hWsource : W ⊆ f.source :=
    (f.saturation_subset_trapped (sdiff_subset.trans (fun x hx => (hAbad hx).1))).trans
      f.trapped_subset_source
  have hWO : W ⊆ O := fun x hx he => disjoint_left.mp hWdis hx (hFS he)
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
  let Q : ℕ → Finset O := fun n => finiteStageOnAnchorComplement F (P n)
  let R : Finset O := finiteStageOnAnchorComplement F J
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
  have hforward : ∀ n (x : g.source), (x : O) ∈ Q n → g.map x ∈ (Q n ∪ R : Finset O) := by
    intro n x hx
    have hxP : ((x : O) : X) ∈ P n := (mem_finiteStageOnAnchorComplement F (P n) (x : O)).mp hx
    have hv : (g.map x : X) = f.totalize ((x : O) : X) := by
      rw [f.totalize_eq (hVs x.property)]; rfl
    have hstep := hPf n ⟨((x : O) : X), hVs x.property⟩ hxP
    rw [← f.totalize_eq (hVs x.property)] at hstep
    rcases hstep with hh | hh
    · apply Finset.mem_union.mpr
      apply Or.inl
      apply (mem_finiteStageOnAnchorComplement F (P n) (g.map x)).mpr
      rwa [hv]
    · apply Finset.mem_union.mpr
      apply Or.inr
      apply (mem_finiteStageOnAnchorComplement F J (g.map x)).mpr
      rw [hv]
      exact hFJ hh
  have havoid : ∀ n x, x ∈ WO → g.totalize x ∉ (Q n ∪ R : Finset O) := by
    intro n x hx hh
    have hmemW := hfW hx
    apply disjoint_left.mp hWdis hmemW
    rcases Finset.mem_union.mp hh with hh | hh
    · have hm := (mem_finiteStageOnAnchorComplement F (P n) (g.totalize x)).mp hh
      rw [hval x hx] at hm
      exact hPS n hm
    · have hm := (mem_finiteStageOnAnchorComplement F J (g.totalize x)).mp hh
      rw [hval x hx] at hm
      exact hJS hm
  have hWne : W.Nonempty := by
    obtain ⟨x, hx, _, _, _, _, _, _, _⟩ := hAstarpos.exists_three
    exact ⟨x, hAW hx⟩
  have hWcontrol : ∀ x ∈ W, ∃ i, f.totalize x ∈ L i ∧
      x ∈ f.finiteObstructionSource hf.2.continuous (D i).carrier (E : Set X) := by
    intro y hy
    obtain ⟨n, x, hx, he⟩ := mem_iUnion.mp hy
    exact hcontrol y (mem_iUnion.mpr ⟨n, x, hx.1, he⟩)
  obtain ⟨T, hT, label, hreg, hcover⟩ := f.countable_regular_cover_of_component_control hf
    (fun i => (D i).carrier) (fun i => (D i).isConnected_carrier) L E hWne hWsource
    (fun x hx he => disjoint_left.mp hWdis (hfW hx) (hJS (hEJ he))) hWcontrol
  let TO : ℕ → TopologicalSpace.Opens O := fun n =>
    ⟨Subtype.val ⁻¹' ((V ⊓ T n : TopologicalSpace.Opens X) : Set X),
      (V ⊓ T n).isOpen.preimage continuous_subtype_val⟩
  have hTJ : ∀ n, ((D (label n)).carrier : Set X) \ (J : Set X) ⊆
      (f.restrictSource (T n) (hT n)).regularValues :=
    fun n _ hy => hreg n ⟨hy.1, fun he => hy.2 (hEJ he)⟩
  choose hTO hregO using fun n => f.regular_piece_on_anchor_complement hf F J hFJ
    V hVs hVO hm hfull (T n) (D (label n)).carrier (hT n) (hTJ n)
  have hcoverO : WO ⊆ ⋃ n, (TO n : Set O) ∩ (j (label n) ∘ g.totalize) ⁻¹' Li (label n) := by
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover hx)
    apply mem_iUnion.mpr
    refine ⟨n, ⟨hWs hx, hn.1⟩, ?_⟩
    change (g.totalize x : X) ∈ L (label n)
    rw [hval x hx]
    exact hn.2
  obtain ⟨C, hC, hstep⟩ := g.exists_uniform_cross_ambient_area_advance_on_cover hg p q j hj hjh
    Di R Li hLic (fun i _ hx => hLD i hx)
  have hAOpos : 0 < p.hyperbolicArea AO :=
    (hAstarpos.openSubtype hAstarm O (hAW.trans hWO)).componentwise_hyperbolicArea_pos hAOm p
  have hAOQ : AO ⊆ closure (⋃ n, (Q n : Set O)) := fun x hx =>
    mem_closure_iUnion_finiteStageOnAnchorComplement F P x (hAstarP hx)
  have hWarea : p.hyperbolicArea WO < ⊤ := by
    have hON : Nonempty O := by
      obtain ⟨x, hx⟩ := hWne
      exact ⟨⟨x, hWO hx⟩⟩
    exact lt_of_le_of_lt (measure_mono (show WO ⊆ (Subtype.val ⁻¹' K : Set O) from
      fun _ hx => hWK hx))
      (p.hyperbolicArea_compl_finset_preimage_compact_lt_top F O (fun _ => Iff.rfl) hON hK)
  apply (ne_of_gt hAOpos)
  apply p.measure_zero_of_finite_model_area_bounds Q
    (finiteStageOnAnchorComplement_monotone F hP) hAOm hAOQ hC
  intro n
  have hs := hstep TO hTO label hregO (Q n) (hforward n) WO hWOm hginj hcoverO (fun x hx =>
    ⟨fun hp => havoid n x hx (Finset.mem_union_left _ hp),
     fun hr => havoid n x hx (Finset.mem_union_right _ hr)⟩)
  have hb := AreaDeficit.finite_area_cancellation_le hAOm (show AO ⊆ WO from fun _ hx => hAW hx)
    (p.finitePunctureDomain_area_finite_of_hyperbolicArea_finite (Q n) hWOm hWarea).ne
    (himageO ▸ (Subset.refl (g.totalize '' WO))) hs
    (show p.domainArea (finitePunctureDomain (Q n)) (g.totalize '' WO) ≤
      p.domainArea (finitePunctureDomain (Q n)) (g.totalize '' WO) + 0 by simp)
  simpa only [zero_add] using hb

end SurfaceDynamics
