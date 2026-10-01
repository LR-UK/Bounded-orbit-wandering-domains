module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/

public import BoundedWanderingDomains.Surfaces.Disconnected.FiniteComponentPositiveArea
public import BoundedWanderingDomains.Surfaces.Disconnected.FiniteComponents
public import BoundedWanderingDomains.Surfaces.Disconnected.ClopenNormality
public import BoundedWanderingDomains.Surfaces.Disconnected.ClopenSourceRestriction
public import BoundedWanderingDomains.Surfaces.SingularEncounters.EmbeddedDiscRestriction
public import BoundedWanderingDomains.Surfaces.RestrictionSaturationBridge

@[expose] public section

/-! # Reduction of compact measured saturations to finitely many ambient components -/

open Set Function Filter MeasureTheory Topology
open AreaDeficit.Surfaces
open scoped Manifold ContDiff

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

theorem no_compact_positive_area_finite_control_disconnected
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
  let M := K ∪ range (fun i => (D i).center)
  have hM : IsCompact M := hK.union (Set.finite_range (fun i => (D i).center)).isCompact
  obtain ⟨O, hOc, hMO, hfinite⟩ := exists_finite_clopen_component_neighborhood hM
  let : Finite (ConnectedComponents O) := hfinite
  let : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  have hKO : K ⊆ O := fun _ hx => hMO (Or.inl hx)
  have hDO : ∀ i, ((D i).carrier : Set X) ⊆ O := by
    intro i
    have hcentre : (D i).center ∈ O := hMO (Or.inr (mem_range_self i))
    exact ((D i).isConnected_carrier.subset_connectedComponent (D i).center_mem).trans
      ((show IsClopen (O : Set X) from ⟨hOc, O.isOpen⟩).connectedComponent_subset hcentre)
  have hLO : ∀ i, L i ⊆ O := fun i => (hLD i).trans (hDO i)
  have hAtr : A ⊆ f.trapped := fun x hx => (hAbad hx).1
  have hsatO : f.saturation A ⊆ O := hsatK.trans hKO
  have hsatS : f.saturation A ⊆ f.source :=
    (f.saturation_subset_trapped hAtr).trans f.trapped_subset_source
  have hsatF : MapsTo f.totalize (f.saturation A) (f.saturation A) := by
    intro x hx
    have hh : f.totalize x ∈ f.totalize '' f.saturation A := ⟨x, hx, rfl⟩
    rw [f.totalize_image_saturation hAtr hdis] at hh
    exact hh.1
  obtain ⟨V, hVs, hVO, hm, hfull⟩ := f.exists_full_restriction_to_open hf O
  let r := f.restrictSource V hVs
  let g := r.restrictAmbient O hVO hm
  have hr := f.isOpenHolomorphic_restrictSource hf V hVs
  have hg := r.isOpenHolomorphic_restrictAmbient hr O hVO hm
  have hsatV : f.saturation A ⊆ V := by
    intro x hx
    apply hfull ⟨x, hsatS hx⟩ (hsatO hx)
    rw [← f.totalize_eq (hsatS hx)]
    exact hsatO (hsatF hx)
  have hAO : A ⊆ O := (f.subset_saturation A).trans hsatO
  let AO : Set O := Subtype.val ⁻¹' A
  let KO : Set O := Subtype.val ⁻¹' K
  have hAOm : MeasurableSet AO := hA.preimage continuous_subtype_val.measurable
  have hKOc : IsCompact KO := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    convert hK using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hKO hx⟩, hx, rfl⟩
  have himageAO : Subtype.val '' AO = A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hAO hx⟩, hx, rfl⟩
  have hrbad : A ⊆ r.trapped \ r.omega :=
    f.subset_restrictSource_trapped_diff_omega_of_saturation_subset V hVs hAbad hsatV
  have hsateq : r.saturation A = f.saturation A :=
    f.restrictSource_saturation_eq_of_saturation_subset V hVs hAtr hsatV
  have hgsat : g.saturation AO ⊆ KO := by
    intro x hx
    apply hsatK
    rw [← hsateq, ← himageAO, ← r.image_restrictAmbient_saturation O hVO hm AO]
    exact ⟨x, hx, rfl⟩
  have hgtrap : AO ⊆ g.trapped := fun x hx =>
    (r.mem_restrictAmbient_trapped_iff O hVO hm x).mpr (hrbad hx).1
  have hgbad : AO ⊆ g.trapped \ g.omega := by
    intro x hx
    refine ⟨hgtrap hx, fun hxo => (hAbad hx).2 ?_⟩
    exact f.restrictSource_omega_subset V hVs
      (r.image_omega_restrictAmbient_of_isClosed O hOc hVO hm ⟨x, hxo, rfl⟩)
  have hdisg : Pairwise (fun n m : ℕ => Disjoint (g.imageAt n AO) (g.imageAt m AO)) := by
    apply r.pairwise_disjoint_imageAt_restrictAmbient O hVO hm AO
    rw [himageAO]
    intro n m hnm
    rw [f.restrictSource_imageAt_eq_of_saturation_subset V hVs hAtr hsatV n,
      f.restrictSource_imageAt_eq_of_saturation_subset V hVs hAtr hsatV m]
    exact hdis hnm
  have hinjg : g.InjectiveOnSaturation AO := by
    apply r.injectiveOnSaturation_restrictAmbient O hVO hm AO
    rw [himageAO]
    exact f.injectiveOnSaturation_restrictSource V hVs hAtr hsatV hinj
  have hVc : IsClosed ((Subtype.val : f.source → X) ⁻¹' (V : Set X)) := by
    have he : (Subtype.val : f.source → X) ⁻¹' (V : Set X) =
        (Subtype.val ⁻¹' (O : Set X)) ∩ f.map ⁻¹' (O : Set X) := by
      ext u
      exact ⟨fun hu => ⟨hVO hu, hm ⟨u, hu⟩⟩, fun hu => hfull u hu.1 hu.2⟩
    rw [he]
    exact (hOc.preimage continuous_subtype_val).inter (hOc.preimage hf.2.continuous)
  let EO : Finset O := ((E.finite_toSet).preimage Subtype.val_injective.injOn).toFinset
  have hEO : ∀ x : O, x ∈ EO ↔ (x : X) ∈ E := fun x => by simp [EO]
  let DO : ι → EmbeddedDisc O := fun i => (D i).restrict O (hDO i)
  let LO : ι → Set O := fun i => Subtype.val ⁻¹' L i
  have hLOc : ∀ i, IsCompact (LO i) := fun i =>
    hOc.isClosedEmbedding_subtypeVal.isCompact_preimage (hL i)
  have hLOD : ∀ i, LO i ⊆ (DO i).carrier := by
    intro i x hx
    rw [(D i).restrict_carrier]
    exact hLD i hx
  apply no_positive_area_finite_control_finitely_many_components g hg hAOm hgbad hdisg hinjg
    (hpos.openSubtype hA O hAO) hKOc hgsat DO EO LO hLOc hLOD
  intro x hx
  have hxf : (x : X) ∈ f.saturation A := by
    rw [← hsateq, ← himageAO, ← r.image_restrictAmbient_saturation O hVO hm AO]
    exact ⟨x, hx, rfl⟩
  have hxs : x ∈ g.source := g.trapped_subset_source (g.saturation_subset_trapped hgtrap hx)
  obtain ⟨i, hfxL, hobs⟩ := hcontrol (x : X) hxf
  have hval : (g.totalize x : X) = f.totalize (x : X) := by
    rw [g.totalize_eq hxs, f.totalize_eq (hVs hxs)]
    rfl
  have hfx : g.totalize x ∈ LO i := by
    change (g.totalize x : X) ∈ L i
    rwa [hval]
  refine ⟨i, hfx, ?_⟩
  let b : g.source := ⟨x, hxs⟩
  have hbD : g.map b ∈ (DO i).carrier := by
    rw [← g.totalize_eq hxs]
    exact hLOD i hfx
  apply (g.mem_finiteObstructionSource_iff hg.2.continuous (DO i).carrier (EO : Set O) b).mpr
  refine ⟨hbD, ?_⟩
  have hsub := r.componentSingularValues_restrictAmbient_subset hr.2.continuous O hVO hm
    hg.2.continuous (DO i).carrier b hbD
  have hDeq : ambientOpen O (DO i).carrier = (D i).carrier := (D i).ambientOpen_restrict_carrier O (hDO i)
  rw [hDeq] at hsub
  have hbr : r.map ((r.restrictAmbientSourceHomeomorph O hVO hm) b) ∈ (D i).carrier := by
    exact hLD i (by change (g.map b : X) ∈ L i; rwa [← g.totalize_eq hxs, hval])
  rw [f.componentSingularValues_restrictSource_clopen_eq hf.2.continuous V hVs hVc
    (D i).carrier _ hbr] at hsub
  have horig := (f.mem_finiteObstructionSource_iff hf.2.continuous (D i).carrier (E : Set X)
    ⟨(x : X), hVs hxs⟩).mp hobs
  intro y hy
  exact (hEO y).mpr (horig.2 (hsub ⟨y, hy, rfl⟩))

end SurfaceDynamics
