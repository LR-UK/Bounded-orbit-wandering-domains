/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CoordinateDiskSelection
import BoundedWanderingDomains.Surfaces.LocalMapRestriction
import BoundedWanderingDomains.Surfaces.SaturationDynamics

/-! # A fixed hyperbolic neighbourhood of a proper compact saturation -/

open Set Function
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X]

/-- A proper compactly contained forward saturation has a relatively compact
source neighbourhood whose source and image lie in the complement of one
closed coordinate disk.  That complement comes with a concrete disc cover. -/
theorem exists_invariant_hyperbolic_neighborhood_of_compact_saturation
    (f : LocalMap X) (hf : IsOpenHolomorphic f) {A K : Set X}
    (hAtrap : A ⊆ f.trapped) (hK : IsCompact K) (hKne : K ≠ Set.univ)
    (hKsource : K ⊆ f.source) (hsatK : f.saturation A ⊆ K) :
    ∃ (D : RiemannDynamics.CoordDisk X)
      (_p : AreaDeficit.Surfaces.DiscCover D.compl)
      (V : TopologicalSpace.Opens X)
      (hVsource : closure (V : Set X) ⊆ f.source),
      closure (f.saturation A) ⊆ V ∧
      closure (V : Set X) ⊆ D.compl ∧
      (∀ x : (f.restrictSource V
        (subset_trans subset_closure hVsource)).source,
        (f.restrictSource V
          (subset_trans subset_closure hVsource)).map x ∈ D.compl) ∧
      IsCompact (closure (V : Set X)) := by
  let C : Set X := closure (f.saturation A)
  have hCK : C ⊆ K := closure_minimal hsatK hK.isClosed
  have hCcompact : IsCompact C :=
    hK.of_isClosed_subset isClosed_closure hCK
  have hCsource : C ⊆ f.source := hCK.trans hKsource
  have hCne : C ≠ Set.univ := by
    intro hC
    apply hKne
    apply eq_univ_iff_forall.mpr
    intro x
    exact hCK (hC.symm ▸ mem_univ x)
  have hforward : MapsTo f.totalize C C :=
    f.totalize_mapsTo_closure_saturation hf.2.continuous hAtrap hCsource
  obtain ⟨D, p, hCD⟩ :=
    exists_discCovered_coordDisk_compl_of_isClosed isClosed_closure hCne
  let T : Set X :=
    (f.source : Set X) ∩ (D.compl : Set X) ∩ f.totalize ⁻¹' (D.compl : Set X)
  have hTopen : IsOpen T := by
    have hpre : IsOpen ((f.source : Set X) ∩
        f.totalize ⁻¹' (D.compl : Set X)) :=
      (f.continuousOn_totalize hf.2.continuous).isOpen_inter_preimage
        f.source.isOpen D.compl.isOpen
    have hopen := (f.source.isOpen.inter D.compl.isOpen).inter hpre
    convert hopen using 1
    ext x
    simp only [T, mem_inter_iff, mem_preimage]
    tauto
  have hCT : C ⊆ T := by
    intro x hx
    exact ⟨⟨hCsource hx, hCD hx⟩, hCD (hforward hx)⟩
  obtain ⟨V0, hVopen, hCV, hVclosure, hVcompact⟩ :=
    exists_open_between_and_isCompact_closure hCcompact hTopen hCT
  let V : TopologicalSpace.Opens X := ⟨V0, hVopen⟩
  have hVsource : closure (V : Set X) ⊆ f.source :=
    hVclosure.trans (fun _ hx => hx.1.1)
  let hVs : (V : Set X) ⊆ f.source :=
    subset_trans subset_closure hVsource
  refine ⟨D, p, V, hVsource, ?_, ?_, ?_, hVcompact⟩
  · exact hCV
  · exact fun x hx => (hVclosure hx).1.2
  · intro x
    have hxT := hVclosure (subset_closure x.property)
    have htotal : f.totalize (x : X) =
        f.map ⟨(x : X), hVs x.property⟩ :=
      f.totalize_eq (hVs x.property)
    change f.map ⟨(x : X), hVs x.property⟩ ∈ D.compl
    rw [← htotal]
    exact hxT.2

end SurfaceDynamics.LocalMap
