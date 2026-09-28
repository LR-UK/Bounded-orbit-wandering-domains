/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.HyperbolicDerivedLimits
import BoundedWanderingDomains.Surfaces.SubsurfaceWanderingComponents
import BoundedWanderingDomains.Surfaces.SubsurfaceRegularValues
import BoundedWanderingDomains.Surfaces.NoEscapeCompactRange
import BoundedWanderingDomains.Surfaces.WanderingAnchorDisk

/-! # The derived-singular-limit theorem on an arbitrary Riemann surface -/

open Set Function Filter Topology OnePoint
open AreaDeficit.Surfaces
open scoped Manifold Topology ContDiff

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X]

theorem nonEscapingWanderingOrbitClusterMeetsDerivedClaim :
    NonEscapingWanderingOrbitClusterMeetsDerivedClaim (X := X) := by
  classical
  let : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  intro f hf U hU hsc z hz hno
  have hztrap := hU.subset_trapped f hz
  let zt : f.trapped := ⟨z, hztrap⟩
  have hcompacteq : ∀ n, f.compactifiedIterate n z = (f.orbit n zt : OnePoint X) :=
    fun n => f.compactifiedIterate_eq_orbit n zt
  obtain ⟨K, hK, hzK⟩ := compact_range_of_no_escaping_subsequence (fun n => f.orbit n zt) (by
    intro hh
    apply hno
    simpa only [hcompacteq] using hh)
  obtain ⟨S, hS0, hScomp, hSimage, hSdis⟩ := hU
  have hzS : ∀ n, f.orbit n zt ∈ S n := fun n =>
    hSimage n ⟨z, hz, f.iterate_eq_some_orbit n zt⟩
  have hSomega : ∀ n, S n ⊆ f.omega := by
    intro n
    obtain ⟨x, hx, hSx⟩ := hScomp n
    rw [hSx]
    exact connectedComponentIn_subset _ _
  have hSo : ∀ n, IsOpen (S n) := by
    intro n
    obtain ⟨x, hx, hSx⟩ := hScomp n
    rw [hSx]
    exact f.isOpen_omega.connectedComponentIn
  have hSsc : ∀ n, IsSimplyConnected (S n) := by
    intro n
    obtain ⟨x, hx, hSx⟩ := hScomp n
    have he : S n = connectedComponentIn f.omega (f.orbit n zt) :=
      hSx.trans (connectedComponentIn_eq (hSx ▸ hzS n))
    rw [he]
    exact hsc n _ ⟨z, hz, f.iterate_eq_some_orbit n zt⟩
  have hfS := f.mapsTo_component_of_imageAt hf hScomp hSimage hz hztrap
  obtain ⟨D, hD⟩ := exists_coordDisk_closedCarrier_subset_diff (hSo 0) (hS0.symm ▸ hz)
  let O := D.compl
  let : IsManifold 𝓘(ℂ) ω X := isManifold_analytic_of_complex
  let p : DiscCover O := Classical.choice (nonempty_discCover_coordDisk_compl D)
  let : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  let : MeasurableSpace O := borel O
  let : BorelSpace O := ⟨rfl⟩
  have hSs : ∀ n, S n ⊆ f.source := fun n => (hSomega n).trans f.omega_subset_source
  have hSO : ∀ n, S (n + 1) ⊆ O := by
    intro n x hx hd
    exact disjoint_left.mp (hSdis (by omega : n + 1 ≠ 0)) hx (hD hd).1
  let V : TopologicalSpace.Opens X :=
    ⟨Subtype.val '' {x : f.source | (x : X) ∈ O ∧ f.map x ∈ O},
      f.source.isOpen.isOpenMap_subtype_val _
        ((O.isOpen.preimage continuous_subtype_val).inter (O.isOpen.preimage hf.2.continuous))⟩
  have hVs : (V : Set X) ⊆ f.source := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hVO : (V : Set X) ⊆ O := by
    rintro x ⟨y, hy, rfl⟩
    exact hy.1
  let r := f.restrictSource V hVs
  have hm : ∀ x : r.source, r.map x ∈ O := by
    intro x
    obtain ⟨y, hy, he⟩ := x.property
    have hey : (⟨(x : X), hVs x.property⟩ : f.source) = y := Subtype.ext he.symm
    change f.map ⟨(x : X), hVs x.property⟩ ∈ O
    rw [hey]
    exact hy.2
  let g := r.restrictAmbient O hVO hm
  have hr := f.isOpenHolomorphic_restrictSource hf V hVs
  have hg := r.isOpenHolomorphic_restrictAmbient hr O hVO hm
  have hfull : ∀ x : f.source, (x : X) ∈ O → f.map x ∈ O → (x : X) ∈ V :=
    fun x hx hy => ⟨x, ⟨hx, hy⟩, rfl⟩
  have hSV : ∀ n, S (n + 1) ⊆ V := by
    intro n x hx
    apply hfull ⟨x, hSs (n + 1) hx⟩ (hSO n hx)
    rw [← f.totalize_eq (hSs (n + 1) hx)]
    exact hSO (n + 1) (hfS (n + 1) hx)
  let z1 := f.trappedMap zt
  have haS : ∀ n, f.orbit n z1 ∈ S (n + 1) := fun n => hzS (n + 1)
  have hz1r : (z1 : X) ∈ r.trapped := f.restrictSource_mem_trapped_of_orbit_mem
    V hVs z1.property (fun n => hSV n (haS n))
  let zo : O := ⟨z1, hSO 0 (haS 0)⟩
  let zg : g.trapped := ⟨zo, (r.mem_restrictAmbient_trapped_iff O hVO hm zo).mpr hz1r⟩
  have hb : ∀ n, (g.orbit n zg : X) = f.orbit (n + 1) zt := by
    intro n
    have hh := r.restrictAmbient_iterate_val O hVO hm n zo
    rw [g.iterate_eq_some_orbit n zg,
      f.restrictSource_iterate_eq_some_orbit V hVs z1.property (fun k => hSV k (haS k)) n] at hh
    exact Option.some.inj hh
  let C := K \ S 0
  have hC : IsCompact C := hK.diff (hSo 0)
  have hCO : C ⊆ O := fun x hx hd => hx.2 (hD hd).1
  have hCOc : IsCompact (Subtype.val ⁻¹' C : Set O) := by
    rw [IsEmbedding.subtypeVal.isCompact_iff, image_preimage_eq_inter_range]
    convert hC using 1
    exact inter_eq_left.mpr (fun x hx => ⟨⟨x, hCO hx⟩, rfl⟩)
  have hgK : ∀ n, g.orbit n zg ∈ (Subtype.val ⁻¹' C : Set O) := by
    intro n
    change (g.orbit n zg : X) ∈ C
    rw [hb]
    exact ⟨hzK (n + 1), fun hh => disjoint_left.mp (hSdis (by omega : n + 1 ≠ 0)) (hzS (n + 1)) hh⟩
  have hR := f.components_restrictAmbient_restrictSource_of_compact_orbit hf O V p hVs hVO hm
    (fun n => S (n + 1)) (fun n => hScomp (n + 1)) (fun n => hSsc (n + 1)) hSV
    (fun n => hfS (n + 1)) zg (fun n => hb n ▸ hzS (n + 1)) hCOc hgK
  have hRdis : Pairwise (fun n m => Disjoint (Subtype.val ⁻¹' S (n + 1) : Set O)
      (Subtype.val ⁻¹' S (m + 1))) := by
    intro n m hnm
    exact (hSdis (by omega : n + 1 ≠ m + 1)).preimage Subtype.val
  obtain ⟨a, ha, hcluster⟩ := compact_wandering_cluster_meets_derived_of_discCover p g hg
    (fun n => Subtype.val ⁻¹' S (n + 1)) (fun n => (hR n).1) (fun n => (hR n).2)
    hRdis zg (fun n => by change (g.orbit n zg : X) ∈ S (n + 1); rw [hb]; exact hzS (n + 1)) hCOc hgK
  obtain ⟨φ, hφ, hlim⟩ := hcluster.tendsto_subseq
  have hlimX : Tendsto (fun n => f.orbit (φ n + 1) zt) atTop (𝓝 (a : X)) := by
    have hh := continuous_subtype_val.continuousAt.tendsto.comp hlim
    change Tendsto (fun n => (g.orbit (φ n) zg : X)) atTop (𝓝 (a : X)) at hh
    simpa only [hb] using hh
  have haS1 : (a : X) ∉ S 1 := by
    apply (hSo 1).isClosed_compl.mem_of_tendsto hlimX
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
    exact fun hh => disjoint_left.mp (hSdis (by omega : φ n + 1 ≠ 1)) (hzS (φ n + 1)) hh
  let B := f.totalize '' D.closedCarrier
  have hBcompact : IsCompact B := D.isCompact_closedCarrier.image_of_continuousOn
    ((f.continuousOn_totalize hf.2.continuous).mono (fun x hx => hSs 0 (hD hx).1))
  have hBS1 : B ⊆ S 1 := by
    rintro y ⟨x, hx, rfl⟩
    exact hfS 0 (hD hx).1
  have hsing : Subtype.val '' g.singularValues ⊆ f.singularValues ∪ B :=
    f.singularValues_restrictAmbient_restrictSource_subset hf O V hVs hVO hm hfull hBcompact.isClosed
      (fun x hx => ⟨x, not_not.mp hx, f.totalize_eq x.property⟩)
  have haderived : (a : X) ∈ derivedSet f.singularValues := by
    have hh := derivedSet_mono _ _ hsing
      (continuous_subtype_val.image_derivedSet Subtype.val_injective ⟨a, ha, rfl⟩)
    rw [derivedSet_union] at hh
    rcases hh with hh | hh
    · exact hh
    · exact False.elim (haS1 (hBS1 (hBcompact.isClosed.closure_subset (derivedSet_subset_closure _ hh))))
  refine ⟨(a : X), haderived, (fun n => φ n + 1), (by intro n m hnm; exact Nat.add_lt_add_right (hφ hnm) 1), ?_⟩
  apply ((OnePoint.continuous_coe.tendsto (a : X)).comp hlimX).congr'
  exact Eventually.of_forall (fun n => (hcompacteq (φ n + 1)).symm)

theorem wanderingDerivedSingularLimitClaim : WanderingDerivedSingularLimitClaim (X := X) :=
  wanderingDerivedSingularLimitClaim_of_nonEscapingClusterMeetsDerived
    nonEscapingWanderingOrbitClusterMeetsDerivedClaim

end SurfaceDynamics
