/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactOrbitFiniteModels
import BoundedWanderingDomains.Surfaces.CompactClusterSeparation
import BoundedWanderingDomains.Surfaces.EventualRegularArea
import BoundedWanderingDomains.Surfaces.SimplyConnectedCoveringDiscs
import BoundedWanderingDomains.Surfaces.ConditionalDiscShrink

/-! # A compact simply connected wandering orbit accumulates at derived singular values -/

open Set Function Filter Topology
open AreaDeficit.Surfaces
open scoped Manifold Topology

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

theorem compact_wandering_cluster_meets_derived_of_discCover
    (p : DiscCover X) (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (R : ℕ → Set X) (hR : ∀ n, f.IsComponent (R n))
    (hRsc : ∀ n, IsSimplyConnected (R n))
    (hdisR : Pairwise (fun n m => Disjoint (R n) (R m)))
    (z : f.trapped) (hzR : ∀ n, f.orbit n z ∈ R n)
    {K : Set X} (hK : IsCompact K) (hzK : ∀ n, f.orbit n z ∈ K) :
    ∃ a ∈ derivedSet f.singularValues, MapClusterPt a atTop (fun n => f.orbit n z) := by
  classical
  letI : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  by_contra hno
  have hsep : ∀ a, MapClusterPt a atTop (fun n => f.orbit n z) → a ∉ derivedSet f.singularValues := by
    intro a ha hs
    exact hno ⟨a, hs, ha⟩
  obtain ⟨L0, L, H, E, hL0, hL, hH, hL0L, hLH, hSE, hevent⟩ :=
    exists_compact_cluster_singular_separation (fun n => f.orbit n z) hK hzK
      f.isClosed_singularValues hsep
  have hzomega : ∀ n, f.orbit n z ∈ f.omega := by
    intro n
    obtain ⟨x, hx, hRx⟩ := hR n
    exact connectedComponentIn_subset _ _ (hRx ▸ hzR n)
  obtain ⟨P, hP, hPf, hPcomp⟩ :=
    f.exists_finite_models_of_compact_normal_orbit hf p z (hzomega 0) hK hzK
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
    letI : SimplyConnectedSpace (U n) := hRsc n
    obtain ⟨q, hq⟩ := (Classical.choice (p.nonempty_subdomain (U n))).exists_centred ⟨_, hzR n⟩
    exact ⟨q, congrArg Subtype.val hq⟩
  choose q hq0 using hq
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
  have hqinj : ∀ n, Injective (q n).projection := by
    intro n
    letI : SimplyConnectedSpace (U n) := hRsc n
    exact (q n).injective_of_simplyConnected
  have hFemb : ∀ n, IsEmbedding (F n) := by
    intro n
    apply IsOpenEmbedding.toIsEmbedding
    rw [isOpenEmbedding_iff_continuous_injective_isOpenMap]
    exact ⟨(hF n).continuous, Subtype.val_injective.comp (hqinj n),
      (U n).isOpen.isOpenMap_subtype_val.comp (q n).isOpenMap⟩
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
  apply f.false_of_eventual_regular_wandering_discs hf p E hH hL hLH hSE P hP hPf U q hUs
  · intro n
    rw [hq0, hPcomp]
    exact hUeq n
  · exact hdisR
  · exact hforward
  · exact hcompact
  · intro r hr hr1
    exact Eventually.of_forall (fun n => (hqinj n).injOn)
  · intro r hr hr1
    have hs : ∀ᶠ n in atTop, Disjoint
        (F (n + 1) '' {w : unitDisc | ‖(w : ℂ)‖ < r}) f.singularValues :=
      (tendsto_add_atTop_nat 1).eventually (havoidS r hr hr1)
    filter_upwards [hs] with n hn
    have hDo : ∀ k, IsOpen (F k '' {w : unitDisc | ‖(w : ℂ)‖ < r}) := fun k =>
      ((U k).isOpen.isOpenMap_subtype_val.comp (q k).isOpenMap) _
        (isOpen_lt continuous_subtype_val.norm continuous_const)
    have hDsc : ∀ k, IsSimplyConnected (F k '' {w : unitDisc | ‖(w : ℂ)‖ < r}) :=
      fun k => (hFemb k).isSimplyConnected_image.mpr (unitDisc_open_radius_simplyConnected hr hr1)
    exact f.injOn_of_simplyConnected_regular_image hf (hDo n) (hDsc n) (hDo (n + 1))
      (hDsc (n + 1)) (by rintro x ⟨w, hw, rfl⟩; exact hUs n ((q n).projection w).property)
      (hforward r hr1 n) (fun x hx hs => disjoint_left.mp hn hx hs)
  · intro r hr hr1
    have hh := p.disjoint_disc_images_eventually_in_cover hK F hF hF0 hdisF
      (fun x : X => (chartAt ℂ x).source) (fun x => (chartAt ℂ x).open_source)
      (fun x hx => mem_iUnion.mpr ⟨x, mem_chart_source ℂ x⟩) hr1
    filter_upwards [hh] with n hn
    obtain ⟨x, hx⟩ := hn
    exact ⟨chartAt ℂ x, (mdifferentiable_chart (I := 𝓘(ℂ)) x).1, fun w hw => hx w hw.le⟩

end SurfaceDynamics

#print axioms SurfaceDynamics.compact_wandering_cluster_meets_derived_of_discCover
