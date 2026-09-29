module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.TargetAnchors
public import BoundedWanderingDomains.Surfaces.SingularEncounters.AnchorRegularPieces
public import BoundedWanderingDomains.Surfaces.SingularEncounters.PositiveAreaFiniteControl
public import BoundedWanderingDomains.Surfaces.AlmostEverywhere.ThreePointHyperbolization
public import BoundedWanderingDomains.Surfaces.SubsurfaceCompactNormal
public import BoundedWanderingDomains.Surfaces.RestrictionSaturationBridge

@[expose] public section

/-! # Finite component control on a noncompact target surface -/

open Set Function Filter MeasureTheory Topology
open AreaDeficit.Surfaces
open scoped Manifold ContDiff

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

theorem no_noncompact_surface_positive_area_saturation_of_finite_component_control
    (hnotcompact : ¬ IsCompact (univ : Set X))
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
  obtain ⟨a₀, _, b₀, _, hb₀, _, _, _, _⟩ := hpos.exists_three
  let : Nontrivial X := ⟨⟨a₀, b₀, Ne.symm hb₀⟩⟩
  let : Infinite X := Set.infinite_univ_iff.mp
    ((infinite_of_mem_nhds a₀ ((chartAt ℂ a₀).open_source.mem_nhds (mem_chart_source ℂ _))).mono
      (subset_univ _))
  let : IsManifold 𝓘(ℂ) ω X := isManifold_analytic_of_complex
  let M := K ∪ ⋃ i, L i
  have hM : IsCompact M := hK.union (isCompact_iUnion hL)
  obtain ⟨F, hFcard, hMF⟩ := exists_three_anchors_disjoint_proper_compact hM
    (fun he => hnotcompact (he ▸ hM))
  let O := anchorComplement F
  let : ConnectedSpace O := Subtype.connectedSpace (RiemannDynamics.isConnected_compl_finset F)
  let : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  let p : DiscCover O := Classical.choice (DiscCover.nonempty_compl_three_on_any_surface F hFcard)
  have hKO : K ⊆ O := fun _ hx => disjoint_left.mp hMF (Or.inl hx)
  have hLO : ∀ i, L i ⊆ O := fun i _ hx =>
    disjoint_left.mp hMF (Or.inr (mem_iUnion.mpr ⟨i, hx⟩))
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
    refine ⟨hgtrap hx, ?_⟩
    intro hxo
    let W := componentDomain ⟨g.omega, g.isOpen_omega⟩ x
    let : ConnectedSpace W := componentDomain_connected hxo
    have hxW : x ∈ W := mem_componentDomain hxo
    have hWtr : (W : Set O) ⊆ g.trapped :=
      (connectedComponentIn_subset _ _).trans (g.omega_subset_trapped_interior.trans interior_subset)
    have hxK : ∀ n, g.orbit n ⟨x, hWtr hxW⟩ ∈ KO := fun n =>
      hgsat (mem_iUnion.mpr ⟨n, x, hx, g.iterate_eq_some_orbit n ⟨x, hWtr hxW⟩⟩)
    have hnormal := r.image_connected_trapped_open_subset_omega_of_compact_orbit hr O p
      hVO hm W hWtr ⟨x, hxW⟩ hKOc hxK
    exact (hAbad hx).2 (f.restrictSource_omega_subset V hVs (hnormal ⟨x, hxW, rfl⟩))
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
  let J := E ∪ F.image f.totalize
  let JO := finiteStageOnAnchorComplement F J
  have hEJ : (E : Set X) ⊆ (J : Set X) := Finset.subset_union_left
  have hFJ : f.totalize '' (F : Set X) ⊆ (J : Set X) := by
    rintro y ⟨x, hx, rfl⟩
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  let DO : ι → TopologicalSpace.Opens O := fun i =>
    ⟨Subtype.val ⁻¹' ((D i).carrier : Set X), (D i).carrier.isOpen.preimage continuous_subtype_val⟩
  let LO : ι → Set O := fun i => Subtype.val ⁻¹' L i
  have hLOc : ∀ i, IsCompact (LO i) := by
    intro i
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    convert hL i using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hLO i hx⟩, hx, rfl⟩
  apply no_compact_positive_hyperbolic_area_saturation_of_regular_covers p g hg
    hAOm hgbad hdisg hinjg (hpos.hyperbolicArea_pos_openSubtype hA O hAO p)
    hKOc hgsat DO JO LO hLOc (fun i _ hx => hLD i hx)
  intro W hWne hWsat havoid
  have hWsource : W ⊆ g.source :=
    hWsat.trans ((g.saturation_subset_trapped hgtrap).trans g.trapped_subset_source)
  have hWorig : Subtype.val '' W ⊆ f.saturation A := by
    rintro y ⟨x, hx, rfl⟩
    rw [← hsateq, ← himageAO, ← r.image_restrictAmbient_saturation O hVO hm AO]
    exact ⟨x, hWsat hx, rfl⟩
  have hval : ∀ x ∈ W, (g.totalize x : X) = f.totalize (x : X) := by
    intro x hx
    rw [g.totalize_eq (hWsource hx), f.totalize_eq (hVs (hWsource hx))]
    rfl
  have havoidE : ∀ x ∈ Subtype.val '' W, f.totalize x ∉ E := by
    rintro _ ⟨x, hx, rfl⟩ he
    apply havoid x hx
    apply (mem_finiteStageOnAnchorComplement F J (g.totalize x)).mpr
    rw [hval x hx]
    exact hEJ he
  obtain ⟨T, hT, label, hreg, hcover⟩ := f.countable_regular_cover_of_component_control hf
    (fun i => (D i).carrier) (fun i => (D i).isConnected_carrier) L E
    (hWne.image Subtype.val) (hWorig.trans hsatS) havoidE
    (fun x hx => hcontrol x (hWorig hx))
  let TO : ℕ → TopologicalSpace.Opens O := fun n =>
    ⟨Subtype.val ⁻¹' ((V ⊓ T n : TopologicalSpace.Opens X) : Set X),
      (V ⊓ T n).isOpen.preimage continuous_subtype_val⟩
  have hTJ : ∀ n, ((D (label n)).carrier : Set X) \ (J : Set X) ⊆
      (f.restrictSource (T n) (hT n)).regularValues :=
    fun n _ hy => hreg n ⟨hy.1, fun he => hy.2 (hEJ he)⟩
  choose hTO hregO using fun n => f.regular_piece_on_anchor_complement hf F J hFJ
    V hVs hVO hm hfull (T n) (D (label n)).carrier (hT n) (hTJ n)
  refine ⟨TO, hTO, label, hregO, ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover ⟨x, hx, rfl⟩)
  apply mem_iUnion.mpr
  refine ⟨n, ⟨hWsource hx, hn.1⟩, ?_⟩
  change (g.totalize x : X) ∈ L (label n)
  rw [hval x hx]
  exact hn.2

end SurfaceDynamics
