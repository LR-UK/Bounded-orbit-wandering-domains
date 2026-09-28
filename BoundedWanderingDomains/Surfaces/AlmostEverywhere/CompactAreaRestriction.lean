/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.AlmostEverywhere.CompactDerivedArea
import BoundedWanderingDomains.Surfaces.AlmostEverywhere.ThreePointHyperbolization
import BoundedWanderingDomains.Surfaces.AnchorComplementModels
import BoundedWanderingDomains.Surfaces.SubsurfaceCompactNormal
import BoundedWanderingDomains.Surfaces.SubsurfaceRegularValues
import BoundedWanderingDomains.Surfaces.RestrictionSaturationBridge

/-! # Ambient restriction and the compact area theorem -/

open Set Function Filter MeasureTheory TopologicalSpace
open AreaDeficit.Surfaces
open scoped Topology Manifold ContDiff

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

theorem no_proper_compact_positive_area_saturation_away_from_derived
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A K : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A) (hpos : HasPositiveChartArea A)
    (hK : IsCompact K) (hKne : K ≠ univ)
    (havoid : Disjoint K (derivedSet f.singularValues)) (hsatK : f.saturation A ⊆ K) : False := by
  classical
  obtain ⟨a₀, _, b₀, _, hb₀, _, _, _, _⟩ := hpos.exists_three
  let : Nontrivial X := ⟨⟨a₀, b₀, Ne.symm hb₀⟩⟩
  let : Infinite X := Set.infinite_univ_iff.mp
    ((infinite_of_mem_nhds a₀ ((chartAt ℂ a₀).open_source.mem_nhds (mem_chart_source ℂ _))).mono
      (subset_univ _))
  let : IsManifold 𝓘(ℂ) ω X := isManifold_analytic_of_complex
  obtain ⟨a, ha⟩ : Kᶜ.Nonempty := Set.nonempty_compl.mpr hKne
  have hKinf : Kᶜ.Infinite := infinite_of_mem_nhds a (hK.isClosed.isOpen_compl.mem_nhds ha)
  obtain ⟨b, hbK, hba⟩ := hKinf.exists_notMem_finite (Set.finite_singleton a)
  obtain ⟨c, hcK, hcab⟩ := hKinf.exists_notMem_finite (Set.toFinite {a, b})
  have hab : a ≠ b := by simpa only [mem_singleton_iff, ne_eq, eq_comm] using hba
  have hac : a ≠ c := fun he => hcab (by simp [he])
  have hbc : b ≠ c := fun he => hcab (by simp [he])
  let F : Finset X := {a, b, c}
  have hFcard : F.card = 3 := by simp [F, hab, hac, hbc]
  let O := anchorComplement F
  let : ConnectedSpace O := Subtype.connectedSpace (RiemannDynamics.isConnected_compl_finset F)
  let : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  let p : DiscCover O := Classical.choice (DiscCover.nonempty_compl_three_on_any_surface F hFcard)
  have hKO : K ⊆ O := by
    intro x hx hxF
    change x ∈ F at hxF
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hxF
    rcases hxF with rfl | rfl | rfl
    · exact ha hx
    · exact hbK hx
    · exact hcK hx
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
  obtain ⟨H, E, hH, hKH, hSE⟩ :=
    compact_singular_separation_of_disjoint_derived hK f.isClosed_singularValues havoid
  let J : Finset X := E ∪ F.image f.totalize
  let JO := finiteStageOnAnchorComplement F J
  let HO : Set O := Subtype.val ⁻¹' H
  have hsing : g.singularValues ⊆ HO ∪ (JO : Set O) := by
    intro y hy
    have hh := f.singularValues_restrictAmbient_restrictSource_subset hf O V hVs hVO hm hfull
      (F.image f.totalize).finite_toSet.isClosed
      (fun x hx => by
        apply Finset.mem_image.mpr
        refine ⟨(x : X), not_not.mp hx, ?_⟩
        exact f.totalize_eq x.property)
      ⟨y, hy, rfl⟩
    rcases hh with hs | hj
    · rcases hSE hs with hHmem | hEmem
      · exact Or.inl hHmem
      · exact Or.inr ((mem_finiteStageOnAnchorComplement F J y).mpr
          (Finset.mem_union_left _ hEmem))
    · exact Or.inr ((mem_finiteStageOnAnchorComplement F J y).mpr
        (Finset.mem_union_right _ hj))
  exact no_compact_positive_hyperbolic_area_saturation_of_singular_separation p g hg
    hAOm hgbad hdisg hinjg (hpos.hyperbolicArea_pos_openSubtype hA O hAO p) hKOc HO JO
    (hH.preimage continuous_subtype_val) (disjoint_left.mpr (fun _ hx hh => disjoint_left.mp hKH hx hh))
    hsing hgsat

end SurfaceDynamics

open Set Function MeasureTheory
open scoped Manifold Topology

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

theorem no_compact_positive_area_saturation_away_from_derived
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A K : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A) (hpos : HasPositiveChartArea A)
    (hK : IsCompact K) (havoid : Disjoint K (derivedSet f.singularValues))
    (hsatK : f.saturation A ⊆ K) : False := by
  by_cases hKeq : K = univ
  · subst K
    let : CompactSpace X := ⟨hK⟩
    have hfin : f.singularValues.Finite := by
      simpa using compact_inter_finite_of_avoids_derived hK havoid
    exact false_of_compact_finite_singular_positive_area_wandering f hf hfin hA hAbad hdis hinj hpos
  · exact no_proper_compact_positive_area_saturation_away_from_derived f hf hA hAbad hdis hinj
      hpos hK hKeq havoid hsatK

end SurfaceDynamics
