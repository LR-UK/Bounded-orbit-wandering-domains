/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.HyperbolicOrbitEscape
import BoundedWanderingDomains.Surfaces.SubsurfaceOrbitRestriction
import BoundedWanderingDomains.Surfaces.LocalMapSubsurface
import BoundedWanderingDomains.Surfaces.WanderingAnchorDisk

/-! # No compact wandering orbit on an arbitrary Riemann surface -/

open Set Function Topology
open AreaDeficit.Surfaces
open scoped Manifold Topology ContDiff

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X]

theorem noCompactWanderingOrbitClaim : NoCompactWanderingOrbitClaim (X := X) := by
  classical
  letI : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  intro f hf U hU z hz K hK hKs
  by_contra hescape
  push_neg at hescape
  obtain ⟨S, hS0, hScomp, hSimage, hSdis⟩ := hU
  have hUomega : U ⊆ f.omega := by
    obtain ⟨w, hw, he⟩ := hScomp 0
    rw [← hS0, he]
    exact connectedComponentIn_subset _ _
  have hUtrap : U ⊆ f.trapped := hUomega.trans
    (f.omega_subset_trapped_interior.trans interior_subset)
  have hUopen : IsOpen U := by
    obtain ⟨w, hw, he⟩ := hScomp 0
    rw [← hS0, he]
    exact f.isOpen_omega.connectedComponentIn
  let zt : f.trapped := ⟨z, hUtrap hz⟩
  have hzK : ∀ n, f.orbit n zt ∈ K :=
    f.orbit_mem_of_compactifiedIterate_mem_image zt.property hescape
  obtain ⟨D, hD⟩ := exists_coordDisk_closedCarrier_subset_diff hUopen hz
  let O := D.compl
  letI : IsManifold 𝓘(ℂ) ω X := isManifold_analytic_of_complex
  let p : DiscCover O := Classical.choice (nonempty_discCover_coordDisk_compl D)
  letI : ConnectedSpace O := Subtype.connectedSpace (RiemannDynamics.isConnected_coordDisk_compl D)
  letI : NoncompactSpace O := RiemannDynamics.noncompactSpace_coordDisk_compl D
  letI : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  letI : MeasurableSpace O := borel O
  letI : BorelSpace O := ⟨rfl⟩
  have hSO : ∀ n, S (n + 1) ⊆ O := by
    intro n x hx hxd
    exact disjoint_left.mp (hSdis (by omega : n + 1 ≠ 0)) hx
      (hS0.symm ▸ (hD hxd).1)
  let z1 : f.trapped := f.trappedMap zt
  let a : ℕ → X := fun n => f.orbit n z1
  have haS : ∀ n, a n ∈ S (n + 1) := fun n =>
    hSimage (n + 1) ⟨z, hz, f.iterate_eq_some_orbit (n + 1) zt⟩
  have haK : ∀ n, a n ∈ K \ U := by
    intro n
    refine ⟨hzK (n + 1), ?_⟩
    intro hh
    exact disjoint_left.mp (hSdis (by omega : n + 1 ≠ 0)) (haS n) (hS0.symm ▸ hh)
  let C := closure (f.saturation ({(z1 : X)} : Set X))
  have hCK : C ⊆ K \ U := by
    apply closure_minimal _ (hK.isClosed.sdiff hUopen)
    rintro x hx
    obtain ⟨n, y, hy, he⟩ := mem_iUnion.mp hx
    have hyz : y = (z1 : X) := mem_singleton_iff.mp hy
    subst y
    have hex : x = a n := Option.some.inj (he.symm.trans (f.iterate_eq_some_orbit n z1))
    exact hex ▸ haK n
  have hCc : IsCompact C := hK.of_isClosed_subset isClosed_closure
    (hCK.trans (fun _ hx => hx.1))
  have hCs : C ⊆ f.source := hCK.trans (fun _ hx => hKs hx.1)
  have hCO : C ⊆ O := fun x hx hd => (hCK hx).2 (hD hd).1
  have haC : ∀ n, a n ∈ C := fun n => subset_closure
    (mem_iUnion.mpr ⟨n, (z1 : X), mem_singleton _, f.iterate_eq_some_orbit n z1⟩)
  have hCf : MapsTo f.totalize C C := f.totalize_mapsTo_closure_saturation hf.2.continuous
    (singleton_subset_iff.mpr z1.property) hCs
  obtain ⟨V, hVs, hCV, hVO, hVc, hmap⟩ :=
    f.exists_invariant_neighborhood_in_subsurface hf O hCc hCs hCO hCf
  let hVsource : (V : Set X) ⊆ f.source := subset_closure.trans hVs
  let r := f.restrictSource V hVsource
  let hsourceO : (r.source : Set X) ⊆ O := fun x hx => hVO (subset_closure hx)
  let g := r.restrictAmbient O hsourceO hmap
  have hr : IsOpenHolomorphic r := f.isOpenHolomorphic_restrictSource hf V hVsource
  have hg : IsOpenHolomorphic g := r.isOpenHolomorphic_restrictAmbient hr O hsourceO hmap
  have hWopen : IsOpen (f.imageAt 1 U) := by
    rw [← f.totalize_image_imageAt hUtrap 0, f.imageAt_zero]
    exact f.isOpen_image_totalize hf.1 hUopen (hUtrap.trans f.trapped_subset_source)
  let W : TopologicalSpace.Opens X := ⟨f.imageAt 1 U, hWopen⟩
  have hWtrap : (W : Set X) ⊆ f.trapped := f.imageAt_subset_trapped hUtrap 1
  have hWO : ∀ n (w : W), f.orbit n ⟨w, hWtrap w.property⟩ ∈ O := by
    intro n w
    obtain ⟨y, hy, he⟩ := w.property
    have hytrap := hUtrap hy
    have hew : f.map ⟨y, f.trapped_subset_source hytrap⟩ = (w : X) := by
      rw [f.iterate_succ 0 y (f.trapped_subset_source hytrap)] at he
      exact Option.some.inj he
    apply hSO n
    apply hSimage (n + 1)
    refine ⟨y, hy, ?_⟩
    rw [f.iterate_succ n y (f.trapped_subset_source hytrap), hew]
    exact f.iterate_eq_some_orbit n ⟨w, hWtrap w.property⟩
  have hz1W : (z1 : X) ∈ W := ⟨z, hz, f.iterate_eq_some_orbit 1 zt⟩
  have hz1int : (z1 : X) ∈ interior r.trapped :=
    f.mem_interior_trapped_restrict_of_subsurface_orbit hf O p W hWtrap hWO V hVsource
      hz1W hCc hCO hCV haC
  let zO : O := ⟨z1, hCO (haC 0)⟩
  have hzOint : zO ∈ interior g.trapped := by
    have hopen : IsOpen (Subtype.val ⁻¹' interior r.trapped : Set O) :=
      isOpen_interior.preimage continuous_subtype_val
    apply (interior_maximal (t := Subtype.val ⁻¹' interior r.trapped) _ hopen) hz1int
    intro x hx
    exact (r.mem_restrictAmbient_trapped_iff O hsourceO hmap x).mpr (interior_subset hx)
  have hzOtrap : zO ∈ g.trapped := interior_subset hzOint
  have hb : ∀ n, (g.orbit n ⟨zO, hzOtrap⟩ : X) = a n := by
    intro n
    have hh := r.restrictAmbient_iterate_val O hsourceO hmap n zO
    rw [g.iterate_eq_some_orbit n ⟨zO, hzOtrap⟩] at hh
    rw [f.restrictSource_iterate_eq_some_orbit V hVsource z1.property
      (fun k => hCV (haC k)) n] at hh
    exact Option.some.inj hh
  have hVpre : IsCompact (Subtype.val ⁻¹' closure (V : Set X) : Set O) := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, image_preimage_eq_inter_range]
    convert hVc using 1
    exact inter_eq_left.mpr (fun x hx => ⟨⟨x, hVO hx⟩, rfl⟩)
  have hgc : IsCompact (closure (g.source : Set O)) := hVpre.of_isClosed_subset
    isClosed_closure (closure_minimal (fun x hx => subset_closure hx)
      (isClosed_closure.preimage continuous_subtype_val))
  have hgo : g.omega = interior g.trapped := by
    have hh := g.omega_restrictSource_eq_interior_trapped hg ⊤ g.source p.top
      (Subset.refl _) hgc (fun _ _ => mem_univ _)
    exact hh
  have hTT : MapsTo g.totalize (interior g.trapped) (interior g.trapped) := by
    simpa only [g.trappedSet_totalize_eq_trapped] using
      (AreaDeficit.trapped_interior_forward (f := g.totalize) (V := (g.source : Set O))
        (fun A hAs hAo => g.isOpen_image_totalize hg.1 hAo hAs))
  have hborbit : ∀ n, g.orbit n ⟨zO, hzOtrap⟩ ∈ g.omega := by
    intro n
    rw [hgo, ← g.totalize_iterate_orbit n ⟨zO, hzOtrap⟩]
    exact hTT.iterate n hzOint
  have hgfomega : Subtype.val '' g.omega ⊆ f.omega :=
    f.omega_restrictAmbient_restrictSource_subset hf O V p hVsource hVc hVO hmap
  let R : ℕ → Set O := fun n => connectedComponentIn g.omega (g.orbit n ⟨zO, hzOtrap⟩)
  have hRsub : ∀ n, Subtype.val '' R n ⊆ S (n + 1) := by
    intro n
    obtain ⟨w, hw, hSw⟩ := hScomp (n + 1)
    have hc : IsPreconnected (Subtype.val '' R n : Set X) :=
      isPreconnected_connectedComponentIn.image _ continuous_subtype_val.continuousOn
    have haR : a n ∈ Subtype.val '' R n :=
      ⟨g.orbit n ⟨zO, hzOtrap⟩, mem_connectedComponentIn (hborbit n), hb n⟩
    have hsub : Subtype.val '' R n ⊆ f.omega :=
      (image_mono (connectedComponentIn_subset _ _)).trans hgfomega
    calc
      Subtype.val '' R n ⊆ connectedComponentIn f.omega (a n) :=
        hc.subset_connectedComponentIn haR hsub
      _ = S (n + 1) := (connectedComponentIn_eq (hSw ▸ haS n)).symm.trans hSw.symm
  have hRdis : Pairwise (fun n m => Disjoint (R n) (R m)) := by
    intro n m hnm
    apply disjoint_left.mpr
    intro x hxn hxm
    exact disjoint_left.mp (hSdis (by omega : n + 1 ≠ m + 1))
      (hRsub n ⟨x, hxn, rfl⟩) (hRsub m ⟨x, hxm, rfl⟩)
  have hCOc : IsCompact (Subtype.val ⁻¹' C : Set O) := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, image_preimage_eq_inter_range]
    convert hCc using 1
    exact inter_eq_left.mpr (fun x hx => ⟨⟨x, hCO hx⟩, rfl⟩)
  apply compactComponentOrbitImpossibleClaim_of_discCover p g hg R
    (fun n => ⟨_, hborbit n, rfl⟩) hRdis zO hzOtrap
    (fun n => mem_connectedComponentIn (hborbit n)) _ hCOc (fun x hx => hCV hx)
  intro n
  change (g.orbit n ⟨zO, hzOtrap⟩ : X) ∈ C
  rw [hb]
  exact haC n

end SurfaceDynamics
