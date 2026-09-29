module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.LocalCompactModelPatches
public import BoundedWanderingDomains.Surfaces.InvariantSubsurface
public import BoundedWanderingDomains.Surfaces.LocalMapSubsurface
public import BoundedWanderingDomains.Surfaces.PositiveAreaFinalReduction
public import BoundedWanderingDomains.Surfaces.UniformizationBridge
public import Mathlib.Order.Disjointed

@[expose] public section

/-! # Compact local area advance from finitely many proper patches -/

open Set Function MeasureTheory Topology
open scoped Manifold Topology ENNReal ContDiff

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X]
  [MeasurableSpace X] [BorelSpace X] [DecidableEq X]

omit [ConnectedSpace X] in
/-- The local proper models cover a compact set and their area estimates
assemble after making the cover into a measurable disjoint partition. -/
theorem compactLocalAreaAdvanceClaim : CompactLocalAreaAdvanceClaim (X := X) := by
  intro p f hf V hVcompact hVsource K hK hKV
  have hpatch : ∀ x : K, ∃ (Ks L N : Set X),
      IsCompact Ks ∧ Ks ⊆ f.source ∧ IsCompact L ∧ Ks ⊆ V ∧
      IsOpen N ∧ (x : X) ∈ N ∧ N ⊆ interior Ks ∧
      f.totalize '' N ⊆ L ∧
      Disjoint L (f.map '' frontier (f.sourceCompact Ks)) := by
    intro x
    let xs : f.source :=
      ⟨(x : X), hVsource (subset_closure (hKV x.property))⟩
    simpa only [xs] using f.exists_local_compact_model_patch hf V xs (hKV x.property)
  choose Ks L N hKs hKssource hL hKsV hNopen hxN hNKs hfNL hsep using hpatch
  have hcoverK : K ⊆ ⋃ x : K, N x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxN ⟨x, hx⟩⟩
  obtain ⟨I, hcover⟩ := hK.elim_finite_subcover N hNopen hcoverK
  have hlocal : ∀ x : K, ∃ (E : Finset X) (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ (P : Finset X),
        (∀ y (hy : y ∈ V), y ∈ P →
          f.map ⟨y, hVsource (subset_closure hy)⟩ ∈ P) →
        ∀ W : Set X, MeasurableSet W → W ⊆ interior (Ks x) →
          InjOn f.totalize W → f.totalize '' W ⊆ L x →
          (∀ y ∈ W, f.totalize y ∉ P ∪ E ∧
            f.totalize y ∉ f.map '' frontier (f.sourceCompact (Ks x))) →
          p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain P) W ≤
            p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain P)
              (f.totalize '' W) + C := by
    intro x
    obtain ⟨E, -, hcore⟩ :=
      f.exists_uniform_area_advance_of_local_compact_finite_models p hf V
        (fun y hy => hVsource (subset_closure hy))
        (hKs x) (hKssource x) (hKsV x) (hL x)
    obtain ⟨C, hC, hstep⟩ := hcore (hsep x)
    exact ⟨E, C, hC, hstep⟩
  choose E C hC hstep using hlocal
  let Etot : Finset X := I.biUnion E
  let ι := {x : K // x ∈ I}
  let R : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let idx : Fin (Fintype.card ι) → K := fun i => (R i).val
  let Ctot : ℝ≥0∞ := ∑ i, C (idx i)
  refine ⟨Etot, Ctot, ?_, ?_⟩
  · simp only [Ctot, ENNReal.sum_ne_top]
    intro i _
    exact hC (idx i)
  intro P hforward W hW hWK hinj havoid
  let B : Fin (Fintype.card ι) → Set X := fun i => W ∩ N (idx i)
  let A : Fin (Fintype.card ι) → Set X := disjointed B
  have hB : ∀ i, MeasurableSet (B i) := fun i => hW.inter (hNopen (idx i)).measurableSet
  have hA : ∀ i, MeasurableSet (A i) :=
    fun i => disjointedRec (fun _ j ht => ht.diff (hB j)) (hB i)
  have hAsubB : ∀ i, A i ⊆ B i := disjointed_subset B
  have hAsubW : ∀ i, A i ⊆ W := fun i => (hAsubB i).trans inter_subset_left
  have hApart : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin (Fintype.card ι))) : Set _) A :=
    (disjoint_disjointed B).set_pairwise _
  have hBcover : (⋃ i, B i) = W := by
    apply Set.Subset.antisymm
    · exact iUnion_subset fun i => inter_subset_left
    · intro y hy
      have hyK : y ∈ K := hWK hy
      obtain ⟨x, hxI, hyN⟩ := Set.mem_iUnion₂.mp (hcover hyK)
      let xi : ι := ⟨x, hxI⟩
      let i : Fin (Fintype.card ι) := R.symm xi
      apply mem_iUnion.mpr
      refine ⟨i, hy, ?_⟩
      simpa only [B, idx, i, xi, Equiv.apply_symm_apply] using hyN
  have hAcover : (⋃ i ∈ (Finset.univ : Finset (Fin (Fintype.card ι))), A i) = W := by
    simp only [Finset.mem_univ, iUnion_true]
    rw [iUnion_disjointed, hBcover]
  have hsourceW : W ⊆ f.source :=
    hWK.trans (hKV.trans (fun y hy => hVsource (subset_closure hy)))
  have himageMeas : MeasurableSet (f.totalize '' W) := by
    let : PolishSpace X := AreaDeficit.Surfaces.surfacePolishSpace
    exact hW.image_of_continuousOn_injOn
      ((f.continuousOn_totalize hf.2.continuous).mono hsourceW) hinj
  have hfiA : ∀ i, MeasurableSet (f.totalize '' A i) := by
    intro i
    let : PolishSpace X := AreaDeficit.Surfaces.surfacePolishSpace
    exact (hA i).image_of_continuousOn_injOn
      ((f.continuousOn_totalize hf.2.continuous).mono
        ((hAsubW i).trans hsourceW))
      (hinj.mono (hAsubW i))
  have hassembled := AreaDeficit.Surfaces.finite_patch_area_advance
    (p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain P))
    (p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain P))
    (Finset.univ : Finset (Fin (Fintype.card ι))) A (fun i => C (idx i))
    (fun i _ => hA i) (fun i _ => hfiA i) (fun i _ => hAsubW i)
    hApart hAcover hinj (fun i _ => ?_)
  · calc
      p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain P) W
          ≤ p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain P)
              (f.totalize '' W) + ∑ i, C (idx i) := hassembled
      _ ≤ p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain (P ∪ Etot))
              (f.totalize '' W) + ∑ i, C (idx i) := by
        have hmono :
            p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain P)
                (f.totalize '' W) ≤
              p.domainArea
                (AreaDeficit.Surfaces.finitePunctureDomain (P ∪ Etot))
                (f.totalize '' W) := p.domainArea_mono_on
          (AreaDeficit.Surfaces.finitePunctureDomain_antitone
            (show P ⊆ P ∪ Etot from Finset.subset_union_left))
          himageMeas (by
          rintro y ⟨x, hx, rfl⟩ hmem
          exact havoid x hx hmem)
        exact add_le_add hmono le_rfl
      _ = p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain (P ∪ Etot))
              (f.totalize '' W) + Ctot := by
        rfl
  · apply hstep (idx i) P hforward (A i) (hA i)
    · exact (hAsubB i).trans (inter_subset_right.trans (hNKs (idx i)))
    · exact hinj.mono (hAsubW i)
    · exact (image_mono ((hAsubB i).trans inter_subset_right)).trans (hfNL (idx i))
    · intro y hy
      have hay := havoid y (hAsubW i hy)
      refine ⟨?_, ?_⟩
      · intro hm
        apply hay
        rcases Finset.mem_union.mp hm with hp | he
        · exact Finset.mem_union_left _ hp
        · exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨idx i, (R i).property, he⟩)
      · intro hh
        apply Set.disjoint_left.mp (hsep (idx i))
          (hfNL (idx i) ⟨y, (hAsubB i hy).2, rfl⟩) hh

omit [ConnectedSpace X] in
/-- The positive-area conclusion on every surface supplied with a
holomorphic universal covering by the unit disc. -/
theorem noCompactPositiveAreaWanderingSetClaim_of_discCover
    (p : AreaDeficit.Surfaces.DiscCover X) :
    NoCompactPositiveAreaWanderingSetClaim (X := X) :=
  noCompactPositiveAreaWanderingSetClaim_of_discCover_areaAdvance p
    compactLocalAreaAdvanceClaim

/-- The same conclusion in the existing universal-cover definition of a
hyperbolic Riemann surface. -/
theorem noCompactPositiveAreaWanderingSetClaim_of_isHyperbolic
    (hX : RiemannDynamics.IsHyperbolic X) :
    NoCompactPositiveAreaWanderingSetClaim (X := X) := by
  let : IsManifold 𝓘(ℂ) ω X :=
    AreaDeficit.Surfaces.isManifold_analytic_of_complex
  exact noCompactPositiveAreaWanderingSetClaim_of_discCover
    (Classical.choice
      (AreaDeficit.Surfaces.nonempty_discCover_of_isHyperbolic hX))

/-- The arbitrary-surface positive-area theorem when the hypothetical
compact saturation is a proper subset of the surface. -/
theorem noProperCompactPositiveAreaWanderingSet
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (A : Set X) (hAmeas : MeasurableSet A)
    (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise
      (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A) (hApos : HasPositiveChartArea A) :
    ¬ ∃ K : Set X, IsCompact K ∧ K ≠ Set.univ ∧
      K ⊆ f.source ∧ f.saturation A ⊆ K := by
  rintro ⟨K, hK, hKne, hKsource, hsatK⟩
  obtain ⟨D, p, V, hVsource, hCV, hVO, hmap, hVcompact⟩ :=
    f.exists_invariant_hyperbolic_neighborhood_of_compact_saturation hf
      (fun x hx => (hAbad hx).1) hK hKne hKsource hsatK
  have hsatV : f.saturation A ⊆ V := subset_closure.trans hCV
  let hVs : (V : Set X) ⊆ f.source :=
    subset_trans subset_closure hVsource
  let r := f.restrictSource V hVs
  let O := D.compl
  let hsourceO : (r.source : Set X) ⊆ O :=
    fun _ hx => hVO (subset_closure hx)
  let g := r.restrictAmbient O hsourceO hmap
  let AO : Set O := (↑) ⁻¹' A
  let : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  let : ConnectedSpace O :=
    Subtype.connectedSpace (RiemannDynamics.isConnected_coordDisk_compl D)
  have hAO : A ⊆ O := by
    intro x hx
    exact hVO (subset_closure (hsatV (f.subset_saturation A hx)))
  have himageAO : ((↑) : O → X) '' AO = A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hAO hx⟩, hx, rfl⟩
  have hAOmeas : MeasurableSet AO :=
    hAmeas.preimage continuous_subtype_val.measurable
  have hrbad : A ⊆ r.trapped \ r.omega :=
    f.subset_restrictSource_trapped_diff_omega_of_saturation_subset
      V hVs hAbad hsatV
  have hgbad : AO ⊆ g.trapped \ g.omega := by
    intro x hx
    refine ⟨?_, ?_⟩
    · exact (r.mem_restrictAmbient_trapped_iff O hsourceO hmap x).mpr
        (hrbad hx).1
    · intro hxomega
      exact (hAbad hx).2
        (f.omega_restrictAmbient_restrictSource_subset hf O V p hVs
          hVcompact hVO hmap ⟨x, hxomega, rfl⟩)
  have hsateq : r.saturation A = f.saturation A :=
    f.restrictSource_saturation_eq_of_saturation_subset V hVs
      (fun x hx => (hAbad hx).1) hsatV
  have hdisg : Pairwise
      (fun n m : ℕ => Disjoint (g.imageAt n AO) (g.imageAt m AO)) := by
    apply r.pairwise_disjoint_imageAt_restrictAmbient O hsourceO hmap AO
    have hdisr : Pairwise
        (fun n m : ℕ => Disjoint (r.imageAt n A) (r.imageAt m A)) := by
      intro n m hnm
      rw [f.restrictSource_imageAt_eq_of_saturation_subset V hVs
          (fun x hx => (hAbad hx).1) hsatV n,
        f.restrictSource_imageAt_eq_of_saturation_subset V hVs
          (fun x hx => (hAbad hx).1) hsatV m]
      exact hdis hnm
    simpa only [himageAO] using hdisr
  have hinjg : g.InjectiveOnSaturation AO := by
    apply r.injectiveOnSaturation_restrictAmbient O hsourceO hmap AO
    have hinjr : r.InjectiveOnSaturation A :=
      f.injectiveOnSaturation_restrictSource V hVs
        (fun x hx => (hAbad hx).1) hsatV hinj
    simpa only [himageAO] using hinjr
  have hAOarea : 0 < p.hyperbolicArea AO :=
    hApos.hyperbolicArea_pos_openSubtype hAmeas O hAO p
  have hg : IsOpenHolomorphic g := by
    apply r.isOpenHolomorphic_restrictAmbient
      (f.isOpenHolomorphic_restrictSource hf V hVs) O hsourceO hmap
  have hnoc :=
    noCompactPositiveHyperbolicAreaWanderingSet_of_discCover_areaAdvance
      p (compactLocalAreaAdvanceClaim (X := O)) g hg AO hAOmeas hgbad
      hdisg hinjg hAOarea
  apply hnoc
  let C : Set X := closure (f.saturation A)
  let CO : Set O := (↑) ⁻¹' C
  have hCK : C ⊆ K := closure_minimal hsatK hK.isClosed
  have hCcompact : IsCompact C :=
    hK.of_isClosed_subset isClosed_closure hCK
  have hCO : C ⊆ O :=
    hCV.trans (fun _ hx => hVO (subset_closure hx))
  have hCOcompact : IsCompact CO := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    rw [image_preimage_eq_inter_range]
    convert hCcompact using 1
    apply inter_eq_left.mpr
    intro x hx
    exact ⟨⟨x, hCO hx⟩, rfl⟩
  have hCOsource : CO ⊆ g.source := by
    intro x hx
    change (x : X) ∈ V
    exact hCV hx
  have hgsat : g.saturation AO ⊆ CO := by
    intro x hx
    change (x : X) ∈ C
    apply subset_closure
    have hx' : (x : X) ∈ r.saturation A := by
      rw [← himageAO,
        ← r.image_restrictAmbient_saturation O hsourceO hmap AO]
      exact ⟨x, hx, rfl⟩
    rwa [hsateq] at hx'
  exact ⟨CO, hCOcompact, hCOsource, hgsat⟩

/-- On a noncompact Riemann surface every compact candidate is proper, so
the preceding reduction proves the exact positive-area target. -/
theorem noCompactPositiveAreaWanderingSetClaim_of_noncompact
    [NoncompactSpace X] :
    NoCompactPositiveAreaWanderingSetClaim (X := X) := by
  intro f hf A hAmeas hAbad hdis hinj hApos
  rintro ⟨K, hK, hKsource, hsatK⟩
  exact noProperCompactPositiveAreaWanderingSet f hf A hAmeas hAbad
    hdis hinj hApos ⟨K, hK, hK.ne_univ, hKsource, hsatK⟩

/-- The exact conclusion also holds on a compact ambient surface whenever
the local map has a proper open source. -/
theorem noCompactPositiveAreaWanderingSet_of_source_ne_top
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (hsource : f.source ≠ ⊤)
    (A : Set X) (hAmeas : MeasurableSet A)
    (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise
      (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A) (hApos : HasPositiveChartArea A) :
    ¬ ∃ K : Set X, IsCompact K ∧ K ⊆ f.source ∧
      f.saturation A ⊆ K := by
  rintro ⟨K, hK, hKsource, hsatK⟩
  have hKne : K ≠ Set.univ := by
    intro hKuniv
    apply hsource
    ext x
    constructor
    · intro _
      trivial
    · intro _
      exact hKsource (hKuniv ▸ Set.mem_univ x)
  exact noProperCompactPositiveAreaWanderingSet f hf A hAmeas hAbad
    hdis hinj hApos ⟨K, hK, hKne, hKsource, hsatK⟩

end SurfaceDynamics
