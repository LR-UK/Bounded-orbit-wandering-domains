/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.EventualCoveringArea
import BoundedWanderingDomains.Surfaces.BakerCoveringDiscs
import BoundedWanderingDomains.Surfaces.LocalCoveringDiscs
import BoundedWanderingDomains.Surfaces.CompactOrbitRestriction
import BoundedWanderingDomains.Surfaces.OrbitEscapeReduction

/-! # Compact wandering orbits are impossible on a noncompact covered surface -/

open Set Function Filter Topology
open AreaDeficit.Surfaces
open scoped Manifold Topology

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X] [NoncompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [DecidableEq X]

theorem compactComponentOrbitImpossibleClaim_of_discCover
    (p : DiscCover X) : CompactComponentOrbitImpossibleClaim (X := X) := by
  classical
  letI : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  intro f hf R hR hdisR z hz hznR K hK hKsource hznK
  let a : ℕ → X := fun n => f.orbit n ⟨z, hz⟩
  have haomega : ∀ n, a n ∈ f.omega := by
    intro n
    obtain ⟨w, hw, hRw⟩ := hR n
    exact connectedComponentIn_subset _ _ (hRw ▸ hznR n)
  obtain ⟨V, hVsource, Pset, hKV, hVc, hPm, hPfin,
    hfront, hPforward, hdisP, hbad, hcompP⟩ :=
    f.exists_boundaryBarrierPackage_in_subsurface hf ⊤ p.top (fun _ _ => mem_univ _) hK hKsource
  let hVs : (V : Set X) ⊆ f.source := subset_closure.trans hVsource
  let g := f.restrictSource V hVs
  have hg : IsOpenHolomorphic g := f.isOpenHolomorphic_restrictSource hf V hVs
  let T : Set X := interior g.trapped
  have homega : g.omega = T := f.omega_restrictSource_eq_interior_trapped hf ⊤ V p.top
    hVs hVc (fun _ _ => mem_univ _)
  have hTomega : T ⊆ f.omega := by
    rw [← homega]
    exact f.restrictSource_omega_subset V hVs
  have hzT : z ∈ T := f.mem_interior_trapped_restrict_of_compact_orbit hf p V hVs
    (f.omega_subset_trapped_interior (haomega 0)) hK hKV hznK
  have hzgt : z ∈ g.trapped := interior_subset hzT
  have hag : ∀ n, g.orbit n ⟨z, hzgt⟩ = a n := by
    intro n
    apply Option.some.inj
    rw [← g.iterate_eq_some_orbit n ⟨z, hzgt⟩]
    exact f.restrictSource_iterate_eq_some_orbit V hVs hz (fun n => hKV (hznK n)) n
  have hTT : MapsTo g.totalize T T := by
    simpa only [g.trappedSet_totalize_eq_trapped] using
      (AreaDeficit.trapped_interior_forward (f := g.totalize) (V := (g.source : Set X))
        (fun D hDs hDo => g.isOpen_image_totalize hg.1 hDo hDs))
  have haT : ∀ n, a n ∈ T := by
    intro n
    have hh := hTT.iterate n hzT
    rwa [g.totalize_iterate_orbit n ⟨z, hzgt⟩, hag n] at hh
  have hag_next : ∀ n, g.totalize (a n) = a (n + 1) := by
    intro n
    rw [← hag n, ← hag (n + 1), g.totalize_eq (g.orbit_mem_source n ⟨z, hzgt⟩),
      g.orbit_succ]
  have haf_next : ∀ n, f.totalize (a n) = a (n + 1) := by
    intro n
    exact (f.totalize_eq (f.orbit_mem_source n ⟨z, hz⟩)).trans (f.orbit_succ n ⟨z, hz⟩).symm
  let U : ℕ → TopologicalSpace.Opens X := fun n => componentDomain ⟨T, isOpen_interior⟩ (a n)
  have haU : ∀ n, a n ∈ U n := fun n => mem_componentDomain (haT n)
  have hUT : ∀ n, (U n : Set X) ⊆ T := fun n => componentDomain_le _ _
  have hUV : ∀ n, (U n : Set X) ⊆ V := fun n =>
    (hUT n).trans (interior_subset.trans g.trapped_subset_source)
  have hUR : ∀ n, (U n : Set X) ⊆ R n := by
    intro n
    obtain ⟨w, hw, hRw⟩ := hR n
    have hzRw : a n ∈ connectedComponentIn f.omega w := hRw ▸ hznR n
    calc
      (U n : Set X) ⊆ connectedComponentIn f.omega (a n) :=
        connectedComponentIn_mono _ hTomega
      _ = R n := (connectedComponentIn_eq hzRw).symm.trans hRw.symm
  have hdisU : Pairwise (fun n m => Disjoint (U n : Set X) (U m)) :=
    fun n m hnm => (hdisR hnm).mono (hUR n) (hUR m)
  have hq : ∀ n, ∃ q : DiscCover (U n), (q.projection discZero : X) = a n := by
    intro n
    letI : ConnectedSpace (U n) := componentDomain_connected (haT n)
    obtain ⟨q, hq⟩ := (Classical.choice (p.nonempty_subdomain (U n))).exists_centred ⟨a n, haU n⟩
    exact ⟨q, congrArg Subtype.val hq⟩
  choose q hq0 using hq
  let F : ℕ → unitDisc → X := fun n w => (q n).projection w
  have hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n) := fun n =>
    (mdifferentiable_subtype_val (U n)).comp (q n).holomorphic
  have hF0 : ∀ n, F n discZero ∈ K := by
    intro n
    change ((q n).projection discZero : X) ∈ K
    rw [hq0]
    exact hznK n
  have hdisF : Pairwise (fun n m => Disjoint (range (F n)) (range (F m))) := by
    intro n m hnm
    exact (hdisU hnm).mono
      (by rintro x ⟨w, rfl⟩; exact ((q n).projection w).property)
      (by rintro x ⟨w, rfl⟩; exact ((q m).projection w).property)
  have hfg : ∀ x ∈ V, f.totalize x = g.totalize x := by
    intro x hx
    rw [f.totalize_eq (hVs hx), g.totalize_eq hx]
    rfl
  have hgU : ∀ n, MapsTo g.totalize (U n) (U (n + 1)) := by
    intro n
    have hconn := isPreconnected_connectedComponentIn.image g.totalize
      ((g.continuousOn_totalize hg.2.continuous).mono (hUV n))
    have hsub : g.totalize '' (U n : Set X) ⊆ T := by
      rintro x ⟨y, hy, rfl⟩
      exact hTT (hUT n hy)
    have hbase : a (n + 1) ∈ g.totalize '' (U n : Set X) :=
      ⟨a n, haU n, hag_next n⟩
    exact mapsTo_iff_image_subset.mpr (hconn.subset_connectedComponentIn hbase hsub)
  have hfU : ∀ n, MapsTo f.totalize (U n) (U (n + 1)) := by
    intro n x hx
    rw [hfg x (hUV n hx)]
    exact hgU n hx
  have hforward : ∀ r : ℝ, r < 1 → ∀ n, MapsTo f.totalize
      (F n '' {w : unitDisc | ‖(w : ℂ)‖ < r})
      (F (n + 1) '' {w : unitDisc | ‖(w : ℂ)‖ < r}) := by
    intro r hr1 n
    exact f.mapsTo_covering_open_radius hf.2 (U n) (U (n + 1)) ((hUV n).trans hVs)
      (q n) (q (n + 1)) (hfU n) (by rw [hq0, hq0, haf_next]) r
  have hembed : ∀ r : ℝ, 0 < r → r < 1 → ∀ᶠ n in atTop,
      InjOn (F n) {w : unitDisc | ‖(w : ℂ)‖ < r} ∧
      IsSimplyConnected (F n '' {w : unitDisc | ‖(w : ℂ)‖ < r}) := by
    intro r hr hr1
    apply AreaDeficit.Surfaces.eventually_covering_disc_embedded p V.isOpen
      (g.mdifferentiableOn_totalize hg.2)
      (fun D hDV hDo => g.isOpen_image_totalize hg.1 hDo hDV) hK hKV U q hF0
    · intro n
      rw [hq0]
      change connectedComponentIn (interior g.trapped) (a n) = _
      rw [← g.trappedSet_totalize_eq_trapped]
      rfl
    · exact hgU
    · intro n
      rw [hq0, hq0, hag_next]
    · exact hdisU
    · exact hr
    · exact hr1
  obtain ⟨B, hBo, hKB, hBV, hBc⟩ := exists_open_between_and_isCompact_closure hK V.isOpen hKV
  have hcompact : ∀ r : ℝ, 0 < r → r < 1 → ∀ᶠ n in atTop,
      F n '' {w : unitDisc | ‖(w : ℂ)‖ < r} ⊆ closure B := by
    intro r hr hr1
    have hh := p.disjoint_disc_images_eventually_in_cover hK F hF hF0 hdisF
      (fun _ : Unit => B) (fun _ => hBo) (by simpa only [iUnion_const] using hKB) hr1
    filter_upwards [hh] with n hn
    obtain ⟨i, hi⟩ := hn
    rintro x ⟨w, hw, rfl⟩
    exact subset_closure (hi w (le_of_lt hw))
  let P : ℕ → Finset X := fun j => (hPfin j).toFinset
  have hPcoe : ∀ j, (P j : Set X) = Pset j := fun j => (hPfin j).coe_toFinset
  have hPmono : Monotone P := fun j k hjk x hx =>
    (hPfin k).mem_toFinset.mpr (hPm hjk ((hPfin j).mem_toFinset.mp hx))
  apply f.false_of_eventual_wandering_covering_discs p hf V hVc hVsource hBc hBV P hPmono
    (fun j x hxV hxP => (hPfin j).mem_toFinset.mpr
      (hPforward j x hxV ((hPfin j).mem_toFinset.mp hxP))) U q
  · intro n
    simp only [hPcoe, hq0]
    have hh := hcompP (a n) (homega.symm ▸ haT n)
    change connectedComponentIn _ (a n) = connectedComponentIn g.omega (a n) at hh
    change connectedComponentIn T (a n) = _
    rw [← homega]
    exact hh.symm
  · exact hdisU
  · exact hforward
  · exact hcompact
  · intro r hr hr1
    filter_upwards [hembed r hr hr1] with n hn
    intro w hw v hv he
    exact hn.1 hw hv (congrArg Subtype.val he)
  · intro r hr hr1
    exact f.eventually_injOn_wandering_discs p hf hK hKsource F hF hF0 hdisF
      (fun n => by
        change f.totalize ((q n).projection discZero) = ((q (n + 1)).projection discZero : X)
        rw [hq0, hq0, haf_next])
      hr hr1
      (fun n => ((U n).isOpen.isOpenMap_subtype_val.comp (q n).isOpenMap) _
        (isOpen_lt continuous_subtype_val.norm continuous_const))
      (hforward r hr1) ((hembed r hr hr1).mono fun n hn => hn.2)
  · intro r hr hr1
    have hh := p.disjoint_disc_images_eventually_in_cover hK F hF hF0 hdisF
      (fun x : X => (chartAt ℂ x).source) (fun x => (chartAt ℂ x).open_source)
      (fun x hx => mem_iUnion.mpr ⟨x, mem_chart_source ℂ x⟩) hr1
    filter_upwards [hh] with n hn
    obtain ⟨x, hx⟩ := hn
    exact ⟨chartAt ℂ x, (mdifferentiable_chart (I := 𝓘(ℂ)) x).1,
      fun w hw => hx w (le_of_lt hw)⟩

end SurfaceDynamics
