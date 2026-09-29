module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.CompactOrbitFiniteModels
public import BoundedWanderingDomains.Surfaces.CompactClusterSeparation
public import BoundedWanderingDomains.Surfaces.EventualRegularArea
public import BoundedWanderingDomains.Surfaces.SimplyConnectedCoveringDiscs
public import BoundedWanderingDomains.Surfaces.ConditionalDiscShrink
public import BoundedWanderingDomains.Surfaces.BKL.ShrinkingFillings
public import BoundedWanderingDomains.Surfaces.SubdomainCover
public import BoundedWanderingDomains.Surfaces.SubsurfaceCompactNormal
public import BoundedWanderingDomains.Surfaces.SaturationDynamics
public import BoundedWanderingDomains.Surfaces.SubsurfaceRegularValues
public import BoundedWanderingDomains.Surfaces.NoEscapeCompactRange
public import BoundedWanderingDomains.Surfaces.WanderingAnchorDisk

@[expose] public section

section

/-! # The area argument for the derived-set theorem from eventually embedded discs -/

open Set Function Filter Topology
open AreaDeficit.Surfaces
open scoped Manifold Topology

namespace SurfaceDynamics.BKL
open SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

theorem compact_wandering_cluster_meets_derived_of_eventual_injectivity
    (p : DiscCover X) (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (U : ℕ → TopologicalSpace.Opens X) (q : ∀ n, DiscCover (U n))
    (hR : ∀ n, f.IsComponent (U n))
    (hdisR : Pairwise (fun n m => Disjoint (U n : Set X) (U m)))
    (z : f.trapped)
    (hq0 : ∀ n, ((q n).projection discZero : X) = f.orbit n z)
    {K : Set X} (hK : IsCompact K) (hzK : ∀ n, f.orbit n z ∈ K)
    (hpinj : ∀ r : ℝ, 0 < r → r < 1 → ∀ᶠ n in atTop,
      InjOn (q n).projection {w : unitDisc | ‖(w : ℂ)‖ < r}) :
    ∃ a ∈ derivedSet f.singularValues, MapClusterPt a atTop (fun n => f.orbit n z) := by
  classical
  let : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  by_contra hno
  have hsep : ∀ a, MapClusterPt a atTop (fun n => f.orbit n z) → a ∉ derivedSet f.singularValues := by
    intro a ha hs
    exact hno ⟨a, hs, ha⟩
  obtain ⟨L0, L, H, E, hL0, hL, hH, hL0L, hLH, hSE, hevent⟩ :=
    exists_compact_cluster_singular_separation (fun n => f.orbit n z) hK hzK
      f.isClosed_singularValues hsep
  have hzR : ∀ n, f.orbit n z ∈ (U n : Set X) := fun n =>
    hq0 n ▸ ((q n).projection discZero).property
  have hzomega : ∀ n, f.orbit n z ∈ f.omega := by
    intro n
    obtain ⟨x, hx, hRx⟩ := hR n
    exact connectedComponentIn_subset _ _ (hRx ▸ hzR n)
  obtain ⟨P, hP, hPf, hPcomp⟩ :=
    f.exists_finite_models_of_compact_normal_orbit hf p z (hzomega 0) hK hzK
  have hUeq : ∀ n, (U n : Set X) = connectedComponentIn f.omega (f.orbit n z) := by
    intro n
    obtain ⟨x, hx, hRx⟩ := hR n
    exact hRx.trans (connectedComponentIn_eq (hRx ▸ hzR n))
  have hUs : ∀ n, (U n : Set X) ⊆ f.source := fun n =>
    (hUeq n ▸ connectedComponentIn_subset _ _).trans f.omega_subset_source
  let F : ℕ → unitDisc → X := fun n w => (q n).projection w
  have hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n) := fun n =>
    (mdifferentiable_subtype_val (U n)).comp (q n).holomorphic
  have hF0 : ∀ n, F n discZero ∈ K := by
    intro n
    change ((q n).projection discZero : X) ∈ K
    rw [hq0]
    exact hzK n
  have hdisF : Pairwise (fun n m => Disjoint (range (F n)) (range (F m))) := by
    intro n m hnm
    exact (hdisR hnm).mono
      (by rintro x ⟨w, rfl⟩; exact ((q n).projection w).property)
      (by rintro x ⟨w, rfl⟩; exact ((q m).projection w).property)
  have hnext : ∀ n, f.totalize (f.orbit n z) = f.orbit (n + 1) z := by
    intro n
    rw [f.totalize_eq (f.orbit_mem_source n z), f.orbit_succ]
  have hfU : ∀ n, MapsTo f.totalize (U n) (U (n + 1)) := by
    intro n
    have hc : IsPreconnected (f.totalize '' (U n : Set X)) := by
      have hUc : IsPreconnected (U n : Set X) := by
        rw [hUeq n]
        exact isPreconnected_connectedComponentIn
      apply hUc.image
      exact (f.continuousOn_totalize hf.2.continuous).mono (hUs n)
    have hb : f.orbit (n + 1) z ∈ f.totalize '' (U n : Set X) :=
      ⟨f.orbit n z, hzR n, hnext n⟩
    have hsub : f.totalize '' (U n : Set X) ⊆ f.omega := by
      rintro x ⟨y, hy, rfl⟩
      apply f.totalize_mapsTo_omega hf
      exact connectedComponentIn_subset _ _ (hUeq n ▸ hy)
    apply mapsTo_iff_image_subset.mpr
    rw [hUeq (n + 1)]
    exact hc.subset_connectedComponentIn hb hsub
  have hforward : ∀ r : ℝ, r < 1 → ∀ n,
      MapsTo f.totalize (F n '' {w : unitDisc | ‖(w : ℂ)‖ < r})
        (F (n + 1) '' {w : unitDisc | ‖(w : ℂ)‖ < r}) := by
    intro r hr1 n
    exact f.mapsTo_covering_open_radius hf.2 (U n) (U (n + 1)) (hUs n)
      (q n) (q (n + 1)) (hfU n) (by rw [hq0, hq0, hnext]) r
  have hcompact : ∀ r : ℝ, 0 < r → r < 1 → ∀ᶠ n in atTop,
      F n '' {w : unitDisc | ‖(w : ℂ)‖ < r} ⊆ L := by
    intro r hr hr1
    have hh := p.eventually_avoids_closed_of_centre hK hL0.isClosed isOpen_interior.isClosed_compl
      (disjoint_left.mpr (fun x hx hn => hn (hL0L hx))) F hF hF0 hdisF hr.le hr1
    filter_upwards [hh, hevent] with n hn hnc
    rintro x ⟨w, hw, rfl⟩
    apply interior_subset
    apply not_not.mp
    exact hn (by change ((q n).projection discZero : X) ∈ L0; rwa [hq0]) w hw.le
  have havoidS : ∀ r : ℝ, 0 < r → r < 1 → ∀ᶠ n in atTop,
      Disjoint (F n '' {w : unitDisc | ‖(w : ℂ)‖ < r}) f.singularValues := by
    intro r hr hr1
    filter_upwards [hcompact r hr hr1, AreaDeficit.eventually_disjoint_finite hdisR E.finite_toSet]
      with n hn hne
    apply disjoint_left.mpr
    intro x hx hs
    rcases hSE hs with hh | he
    · exact disjoint_left.mp hLH (hn hx) hh
    · obtain ⟨w, hw, rfl⟩ := hx
      exact disjoint_left.mp hne ((q n).projection w).property he
  have hsc : ∀ r : ℝ, 0 < r → r < 1 → ∀ᶠ n in atTop,
      IsSimplyConnected (F n '' {w : unitDisc | ‖(w : ℂ)‖ < r}) := by
    intro r hr hr1
    filter_upwards [hpinj r hr hr1] with n hn
    have hi : InjOn (F n) {w : unitDisc | ‖(w : ℂ)‖ < r} := by
      intro x hx y hy he
      exact hn hx hy (Subtype.ext he)
    have hFo : IsOpenMap (F n) :=
      (U n).isOpen.isOpenMap_subtype_val.comp (q n).isOpenMap
    have hRopen : IsOpen {w : unitDisc | ‖(w : ℂ)‖ < r} :=
      isOpen_lt continuous_subtype_val.norm continuous_const
    have he : IsOpenEmbedding
        ({w : unitDisc | ‖(w : ℂ)‖ < r}.domRestrict (F n)) := by
      rw [isOpenEmbedding_iff_continuous_injective_isOpenMap]
      exact ⟨(hF n).continuous.comp continuous_subtype_val, hi.injective,
        hFo.domRestrict hRopen⟩
    have hsci : IsSimplyConnected
        (univ : Set {w : unitDisc | ‖(w : ℂ)‖ < r}) := by
      let := (unitDisc_open_radius_simplyConnected hr hr1).simplyConnectedSpace
      exact (Homeomorph.Set.univ _).toHomotopyEquiv.simplyConnectedSpace
    have hh := he.isEmbedding.isSimplyConnected_image.mpr hsci
    simpa only [image_univ, range_domRestrict] using hh
  apply f.false_of_eventual_regular_wandering_discs hf p E hH hL hLH hSE P hP hPf U q hUs
  · intro n
    rw [hq0, hPcomp]
    exact hUeq n
  · exact hdisR
  · exact hforward
  · exact hcompact
  · intro r hr hr1
    exact hpinj r hr hr1
  · intro r hr hr1
    have hs : ∀ᶠ n in atTop, Disjoint
        (F (n + 1) '' {w : unitDisc | ‖(w : ℂ)‖ < r}) f.singularValues :=
      (tendsto_add_atTop_nat 1).eventually (havoidS r hr hr1)
    have hscnext := (tendsto_add_atTop_nat 1).eventually (hsc r hr hr1)
    filter_upwards [hs, hsc r hr hr1, hscnext] with n hn hnsc hnscnext
    have hDo : ∀ k, IsOpen (F k '' {w : unitDisc | ‖(w : ℂ)‖ < r}) := fun k =>
      ((U k).isOpen.isOpenMap_subtype_val.comp (q k).isOpenMap) _
        (isOpen_lt continuous_subtype_val.norm continuous_const)
    exact f.injOn_of_simplyConnected_regular_image hf (hDo n) hnsc (hDo (n + 1))
      hnscnext (by rintro x ⟨w, hw, rfl⟩; exact hUs n ((q n).projection w).property)
      (hforward r hr1 n) (fun x hx hs => disjoint_left.mp hn hx hs)
  · intro r hr hr1
    have hh := p.disjoint_disc_images_eventually_in_cover hK F hF hF0 hdisF
      (fun x : X => (chartAt ℂ x).source) (fun x => (chartAt ℂ x).open_source)
      (fun x hx => mem_iUnion.mpr ⟨x, mem_chart_source ℂ x⟩) hr1
    filter_upwards [hh] with n hn
    obtain ⟨x, hx⟩ := hn
    exact ⟨chartAt ℂ x, (mdifferentiable_chart (I := 𝓘(ℂ)) x).1, fun w hw => hx w hw.le⟩

end SurfaceDynamics.BKL

end

section

/-! # The derived-singular-limit theorem for arbitrary wandering components -/

open Set Function Filter Topology
open scoped Manifold
open AreaDeficit.Surfaces

namespace SurfaceDynamics

theorem compact_wandering_cluster_meets_derived_without_simpleConnectivity
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [ConnectedSpace X] [NoncompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (p : DiscCover X) (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (R : ℕ → Set X) (hR : ∀ n, f.IsComponent (R n))
    (hdisR : Pairwise (fun n m => Disjoint (R n) (R m)))
    (z : f.trapped) (hzR : ∀ n, f.orbit n z ∈ R n)
    {K : Set X} (hK : IsCompact K) (hzK : ∀ n, f.orbit n z ∈ K) :
    ∃ a ∈ derivedSet f.singularValues, MapClusterPt a atTop (fun n => f.orbit n z) := by
  classical
  let : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  by_contra hno
  have hsep : ∀ a, MapClusterPt a atTop (fun n => f.orbit n z) →
      a ∉ derivedSet f.singularValues := fun a ha hs => hno ⟨a, hs, ha⟩
  have hRo : ∀ n, IsOpen (R n) := by
    intro n
    obtain ⟨x, hx, hRx⟩ := hR n
    rw [hRx]
    exact f.isOpen_omega.connectedComponentIn
  let U : ℕ → TopologicalSpace.Opens X := fun n => ⟨R n, hRo n⟩
  have hUeq : ∀ n, (U n : Set X) = connectedComponentIn f.omega (f.orbit n z) := by
    intro n
    obtain ⟨x, hx, hRx⟩ := hR n
    exact hRx.trans (connectedComponentIn_eq (hRx ▸ hzR n))
  have hUs : ∀ n, (U n : Set X) ⊆ f.source := fun n =>
    (hUeq n ▸ connectedComponentIn_subset _ _).trans f.omega_subset_source
  have hq : ∀ n, ∃ q : DiscCover (U n), (q.projection discZero : X) = f.orbit n z := by
    intro n
    have hUc : IsConnected (U n : Set X) := by
      obtain ⟨x, hx, hRx⟩ := hR n
      change IsConnected (R n)
      rw [hRx]
      exact isConnected_connectedComponentIn_iff.mpr hx
    let : ConnectedSpace (U n) := Subtype.connectedSpace hUc
    obtain ⟨q, hq⟩ := (Classical.choice (p.nonempty_subdomain (U n))).exists_centred ⟨_, hzR n⟩
    exact ⟨q, congrArg Subtype.val hq⟩
  choose q hq0 using hq
  have hnext : ∀ n, f.totalize (f.orbit n z) = f.orbit (n + 1) z := by
    intro n
    rw [f.totalize_eq (f.orbit_mem_source n z), f.orbit_succ]
  have hfU : ∀ n, MapsTo f.totalize (U n) (U (n + 1)) := by
    intro n
    have hc : IsPreconnected (f.totalize '' (U n : Set X)) := by
      have hUc : IsPreconnected (U n : Set X) := by
        rw [hUeq n]
        exact isPreconnected_connectedComponentIn
      exact hUc.image _ ((f.continuousOn_totalize hf.2.continuous).mono (hUs n))
    have hb : f.orbit (n + 1) z ∈ f.totalize '' (U n : Set X) :=
      ⟨f.orbit n z, hzR n, hnext n⟩
    have hsub : f.totalize '' (U n : Set X) ⊆ f.omega := by
      rintro x ⟨y, hy, rfl⟩
      exact f.totalize_mapsTo_omega hf (connectedComponentIn_subset _ _ (hUeq n ▸ hy))
    apply mapsTo_iff_image_subset.mpr
    rw [hUeq (n + 1)]
    exact hc.subset_connectedComponentIn hb hsub
  have hqnext : ∀ n, ((q (n + 1)).projection discZero : X) =
      f.totalize ((q n).projection discZero) := by
    intro n
    rw [hq0, hq0, hnext]
  have hqK : ∀ n, ((q n).projection discZero : X) ∈ K := fun n => (hq0 n).symm ▸ hzK n
  have hqsep : ∀ a, MapClusterPt a atTop (fun n => ((q n).projection discZero : X)) →
      a ∉ derivedSet f.singularValues := by
    simpa only [hq0] using hsep
  have hinj := fun r hr hr1 => BKL.eventually_injective_centered_covers_of_cluster_avoids_derived
    f hf p U q hR hdisR hfU hqnext hK hqK hqsep (r := r) hr hr1
  exact hno (BKL.compact_wandering_cluster_meets_derived_of_eventual_injectivity
    p f hf U q hR hdisR z hq0 hK hzK hinj)

end SurfaceDynamics

end

section

open Set Function Topology
open AreaDeficit.Surfaces
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]

theorem components_restrictAmbient_restrictSource_of_compact_orbit_connected
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (O V : TopologicalSpace.Opens X) [LocallyCompactSpace O] (p : DiscCover O)
    (hVs : (V : Set X) ⊆ f.source) (hVO : (V : Set X) ⊆ O)
    (hm : ∀ x : (f.restrictSource V hVs).source, (f.restrictSource V hVs).map x ∈ O)
    (S : ℕ → Set X) (hS : ∀ n, f.IsComponent (S n))
    (hSV : ∀ n, S n ⊆ V)
    (hforward : ∀ n, MapsTo f.totalize (S n) (S (n + 1)))
    (z : ((f.restrictSource V hVs).restrictAmbient O hVO hm).trapped)
    (hzS : ∀ n, (((f.restrictSource V hVs).restrictAmbient O hVO hm).orbit n z : X) ∈ S n)
    {K : Set O} (hK : IsCompact K)
    (hzK : ∀ n, ((f.restrictSource V hVs).restrictAmbient O hVO hm).orbit n z ∈ K) :
    ∀ n, ((f.restrictSource V hVs).restrictAmbient O hVO hm).IsComponent
      (Subtype.val ⁻¹' S n) := by
  classical
  let : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  let : LocallyPathConnectedSpace O := ChartedSpace.locallyPathConnectedSpace ℂ O
  let r := f.restrictSource V hVs
  let g := r.restrictAmbient O hVO hm
  have hr := f.isOpenHolomorphic_restrictSource hf V hVs
  have hg := r.isOpenHolomorphic_restrictAmbient hr O hVO hm
  have hSomega : ∀ n, S n ⊆ f.omega := by
    intro n
    obtain ⟨x, hx, hSx⟩ := hS n
    rw [hSx]
    exact connectedComponentIn_subset _ _
  have hSo : ∀ n, IsOpen (S n) := by
    intro n
    obtain ⟨x, hx, hSx⟩ := hS n
    rw [hSx]
    exact f.isOpen_omega.connectedComponentIn
  have hStrap : ∀ n, S n ⊆ f.trapped := fun n =>
    (hSomega n).trans (f.omega_subset_trapped_interior.trans interior_subset)
  have hstay : ∀ n y, y ∈ S n → ∀ m, f.totalize^[m] y ∈ S (n + m) := by
    intro n y hy m
    induction m with
    | zero => simpa using hy
    | succ m ih =>
      rw [iterate_succ_apply']
      exact hforward (n + m) ih
  let R : ℕ → TopologicalSpace.Opens O := fun n =>
    ⟨Subtype.val ⁻¹' S n, (hSo n).preimage continuous_subtype_val⟩
  have hRc : ∀ n, IsConnected (R n : Set O) := by
    intro n
    obtain ⟨x, hx, hSx⟩ := hS n
    have hc : IsConnected (S n) := hSx.symm ▸ isConnected_connectedComponentIn_iff.mpr hx
    exact hc.preimage_of_isOpenMap Subtype.val_injective O.isOpen.isOpenMap_subtype_val
      (fun y hy => ⟨⟨y, hVO (hSV n hy)⟩, rfl⟩)
  have hRtrap : ∀ n, (R n : Set O) ⊆ g.trapped := by
    intro n y hy
    apply (r.mem_restrictAmbient_trapped_iff O hVO hm y).mpr
    apply f.restrictSource_mem_trapped_of_orbit_mem V hVs (hStrap n hy)
    intro m
    rw [← f.totalize_iterate_orbit m ⟨(y : X), hStrap n hy⟩]
    exact hSV (n + m) (hstay n y hy m)
  have hshiftK : ∀ n m, g.orbit m (g.trappedMap^[n] z) ∈ K := by
    intro n m
    change ((g.trappedMap^[m]) ((g.trappedMap^[n]) z) : O) ∈ K
    rw [← iterate_add_apply]
    exact hzK (m + n)
  have hRomega : ∀ n, (R n : Set O) ⊆ g.omega := by
    intro n
    let : ConnectedSpace (R n) := Subtype.connectedSpace (hRc n)
    exact g.connected_trapped_open_subset_omega_of_compact_orbit hg p (R n) (hRtrap n)
      ⟨g.orbit n z, hzS n⟩ hK (hshiftK n)
  intro n
  let C := componentDomain ⟨g.omega, g.isOpen_omega⟩ (g.orbit n z)
  have hzn : g.orbit n z ∈ g.omega := hRomega n (hzS n)
  let : ConnectedSpace C := componentDomain_connected hzn
  have hCtrap : (C : Set O) ⊆ g.trapped :=
    (connectedComponentIn_subset _ _).trans (g.omega_subset_trapped_interior.trans interior_subset)
  have hComega : Subtype.val '' (C : Set O) ⊆ f.omega :=
    (r.image_connected_trapped_open_subset_omega_of_compact_orbit hr O p hVO hm C hCtrap
      ⟨g.orbit n z, mem_componentDomain hzn⟩ hK (hshiftK n)).trans
      (f.restrictSource_omega_subset V hVs)
  have hCsub : (C : Set O) ⊆ R n := by
    have hc : IsPreconnected (Subtype.val '' (C : Set O) : Set X) :=
      isPreconnected_connectedComponentIn.image _ continuous_subtype_val.continuousOn
    obtain ⟨x, hx, hSx⟩ := hS n
    have hsub := hc.subset_connectedComponentIn
      (show (g.orbit n z : X) ∈ Subtype.val '' (C : Set O) from
        ⟨g.orbit n z, mem_componentDomain hzn, rfl⟩) hComega
    have he : connectedComponentIn f.omega (g.orbit n z : X) = S n :=
      (connectedComponentIn_eq (hSx ▸ hzS n)).symm.trans hSx.symm
    intro y hy
    change (y : X) ∈ S n
    exact he ▸ hsub ⟨y, hy, rfl⟩
  have hRsub : (R n : Set O) ⊆ C := by
    have hc : IsPreconnected (R n : Set O) :=
      (hRc n).isPreconnected
    exact hc.subset_connectedComponentIn (hzS n) (hRomega n)
  refine ⟨g.orbit n z, hzn, ?_⟩
  exact Subset.antisymm hRsub hCsub

end SurfaceDynamics.LocalMap

end

section

/-! # The derived-singular-limit theorem on an arbitrary Riemann surface -/

open Set Function Filter Topology OnePoint
open AreaDeficit.Surfaces
open scoped Manifold Topology ContDiff

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X]

theorem nonEscapingWanderingOrbitClusterMeetsDerived_without_simpleConnectivity
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (U : Set X)
    (hU : f.IsWanderingComponent U) (z : X) (hz : z ∈ U)
    (hno : ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => f.compactifiedIterate (φ k) z) atTop (𝓝 (∞ : OnePoint X))) :
    ∃ a ∈ derivedSet f.singularValues, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => f.compactifiedIterate (φ k) z) atTop (𝓝 (a : OnePoint X)) := by
  classical
  let : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
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
  have hfS := f.mapsTo_component_of_imageAt hf hScomp hSimage hz hztrap
  obtain ⟨D, hD⟩ := exists_coordDisk_closedCarrier_subset_diff (hSo 0) (hS0.symm ▸ hz)
  let O := D.compl
  let : IsManifold 𝓘(ℂ) ω X := isManifold_analytic_of_complex
  let p : DiscCover O := Classical.choice (nonempty_discCover_coordDisk_compl D)
  let : ConnectedSpace O := Subtype.connectedSpace (RiemannDynamics.isConnected_coordDisk_compl D)
  let : NoncompactSpace O := RiemannDynamics.noncompactSpace_coordDisk_compl D
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
  have hR := f.components_restrictAmbient_restrictSource_of_compact_orbit_connected hf O V p hVs hVO hm
    (fun n => S (n + 1)) (fun n => hScomp (n + 1)) hSV
    (fun n => hfS (n + 1)) zg (fun n => hb n ▸ hzS (n + 1)) hCOc hgK
  have hRdis : Pairwise (fun n m => Disjoint (Subtype.val ⁻¹' S (n + 1) : Set O)
      (Subtype.val ⁻¹' S (m + 1))) := by
    intro n m hnm
    exact (hSdis (by omega : n + 1 ≠ m + 1)).preimage Subtype.val
  obtain ⟨a, ha, hcluster⟩ := compact_wandering_cluster_meets_derived_without_simpleConnectivity p g hg
    (fun n => Subtype.val ⁻¹' S (n + 1)) hR
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

theorem wanderingDerivedSingularLimit_without_simpleConnectivity
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (U : Set X)
    (hU : f.IsWanderingComponent U) (z : X) (hz : z ∈ U) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (Tendsto (fun k => f.compactifiedIterate (φ k) z) atTop (𝓝 (∞ : OnePoint X)) ∨
        ∃ a ∈ derivedSet f.singularValues,
          Tendsto (fun k => f.compactifiedIterate (φ k) z) atTop (𝓝 (a : OnePoint X))) := by
  by_cases hescape : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => f.compactifiedIterate (φ k) z) atTop (𝓝 (∞ : OnePoint X))
  · obtain ⟨φ, hφ, hlim⟩ := hescape
    exact ⟨φ, hφ, Or.inl hlim⟩
  · obtain ⟨a, ha, φ, hφ, hlim⟩ :=
      nonEscapingWanderingOrbitClusterMeetsDerived_without_simpleConnectivity f hf U hU z hz hescape
    exact ⟨φ, hφ, Or.inr ⟨a, ha, hlim⟩⟩

end SurfaceDynamics

end
