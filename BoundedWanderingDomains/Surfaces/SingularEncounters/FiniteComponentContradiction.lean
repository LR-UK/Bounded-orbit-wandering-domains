module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.CompactOrbitFiniteModels
public import BoundedWanderingDomains.Surfaces.ConditionalDiscShrink
public import BoundedWanderingDomains.Surfaces.SingularEncounters.ComponentControl
public import BoundedWanderingDomains.Surfaces.SingularEncounters.EventualComponentArea
public import BoundedWanderingDomains.Surfaces.SingularEncounters.RestrictedInjectivity

@[expose] public section

/-! # The compact wandering-orbit contradiction under finite component control -/

open Set Function Filter Topology
open AreaDeficit.Surfaces
open scoped Manifold

namespace SurfaceDynamics.BKL

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [NoncompactComponents X]

theorem false_of_compact_wandering_finite_component_control
    (p : ComponentwiseDiscCover X) (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (U : ℕ → TopologicalSpace.Opens X) (q : ∀ n, DiscCover (U n))
    (hR : ∀ n, f.IsComponent (U n))
    (hdisR : Pairwise (fun n m => Disjoint (U n : Set X) (U m)))
    (z : f.trapped) (hq0 : ∀ n, ((q n).projection discZero : X) = f.orbit n z)
    {K : Set X} (hK : IsCompact K) (hzK : ∀ n, f.orbit n z ∈ K)
    {ι : Type*} [Fintype ι] (target : ι → TopologicalSpace.Opens X) (E : Finset X)
    (inner : ι → Set X) (hinner : ∀ i, IsCompact (inner i))
    (hinnerTarget : ∀ i, inner i ⊆ target i)
    (hBKL : ∀ R : ℝ, 0 ≤ R → R < 1 → ∀ᶠ n in atTop,
      f.HasComponentPuncturedDisc (E : Set X)
        ((fun w => ((q n).projection w : X)) '' {w : unitDisc | ‖(w : ℂ)‖ ≤ R}))
    (hlocal : ∀ r : ℝ, 0 < r → r < 1 → ∀ᶠ n in atTop,
      ∃ (i : ι) (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source),
        ((target i : Set X) \ (E : Set X) ⊆ (f.restrictSource V hV).regularValues) ∧
        ((fun w => ((q n).projection w : X)) '' {w : unitDisc | ‖(w : ℂ)‖ < r}) ⊆ V ∧
        ((fun w => ((q (n + 1)).projection w : X)) ''
          {w : unitDisc | ‖(w : ℂ)‖ < r}) ⊆ inner i) : False := by
  classical
  let : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
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
  have hpinj : ∀ r : ℝ, 0 < r → r < 1 → ∀ᶠ n in atTop,
      InjOn (q n).projection {w : unitDisc | ‖(w : ℂ)‖ < r} := by
    intro r hr hr1
    exact eventually_injective_centered_covers_of_restricted_covers f hf p U q hR hdisR
      hfU (by intro n; rw [hq0, hq0, hnext]) hK hF0 E.finite_toSet hBKL hr hr1
  obtain ⟨L, hL, hKL, _⟩ := exists_compact_between hK isOpen_univ (subset_univ K)
  have hcompact : ∀ r : ℝ, 0 < r → r < 1 → ∀ᶠ n in atTop,
      F n '' {w : unitDisc | ‖(w : ℂ)‖ < r} ⊆ L := by
    intro r hr hr1
    have hh := p.eventually_avoids_closed_of_centre hK hK.isClosed isOpen_interior.isClosed_compl
      (disjoint_left.mpr (fun x hx hn => hn (hKL hx))) F hF hF0 hdisF hr.le hr1
    filter_upwards [hh] with n hn
    rintro x ⟨w, hw, rfl⟩
    exact interior_subset (not_not.mp (hn (hF0 n) w hw.le))
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
  apply f.false_of_eventual_componentwise_regular_discs hf p target E inner hinner hinnerTarget
    hL P hP hPf U q
  · intro n
    rw [hq0, hPcomp]
    exact hUeq n
  · exact hdisR
  · exact hforward
  · exact hcompact
  · intro r hr hr1
    exact hpinj r hr hr1
  · intro r hr hr1
    have hE := (tendsto_add_atTop_nat 1).eventually
      (AreaDeficit.eventually_disjoint_finite hdisR E.finite_toSet)
    have hscnext := (tendsto_add_atTop_nat 1).eventually (hsc r hr hr1)
    filter_upwards [hlocal r hr hr1, hE, hsc r hr hr1, hscnext]
      with n hn hnE hnsc hnscnext
    obtain ⟨i, V, hV, hreg, hDV, hnextInner⟩ := hn
    have hDo : ∀ k, IsOpen (F k '' {w : unitDisc | ‖(w : ℂ)‖ < r}) := fun k =>
      ((U k).isOpen.isOpenMap_subtype_val.comp (q k).isOpenMap) _
        (isOpen_lt continuous_subtype_val.norm continuous_const)
    apply f.injOn_of_simplyConnected_restricted_regular_image hf V hV
      (hDo n) hnsc (hDo (n + 1)) hnscnext hDV (hforward r hr1 n)
    intro x hx
    apply hreg
    refine ⟨hinnerTarget i (hnextInner hx), ?_⟩
    obtain ⟨w, hw, rfl⟩ := hx
    exact fun he => disjoint_left.mp hnE ((q (n + 1)).projection w).property he
  · intro r hr hr1
    have hh := p.disjoint_disc_images_eventually_in_cover hK F hF hF0 hdisF
      (fun x : X => (chartAt ℂ x).source) (fun x => (chartAt ℂ x).open_source)
      (fun x hx => mem_iUnion.mpr ⟨x, mem_chart_source ℂ x⟩) hr1
    filter_upwards [hh] with n hn
    obtain ⟨x, hx⟩ := hn
    exact ⟨chartAt ℂ x, (mdifferentiable_chart (I := 𝓘(ℂ)) x).1, fun w hw => hx w hw.le⟩
  · intro r hr hr1
    filter_upwards [hlocal r hr hr1] with n hn
    obtain ⟨i, V, hV, hreg, hDV, hnextInner⟩ := hn
    exact ⟨i, V, hV, hreg, hDV, (hforward r hr1 n).image_subset.trans hnextInner⟩

end SurfaceDynamics.BKL
