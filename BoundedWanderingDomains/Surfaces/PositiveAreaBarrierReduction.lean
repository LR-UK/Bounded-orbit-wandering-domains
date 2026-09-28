/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.BoundaryBarrierPackage
import BoundedWanderingDomains.Surfaces.CoordinateDiskSelection
import BoundedWanderingDomains.Surfaces.RestrictionSaturationBridge

/-! # Boundary-puncture reduction for a compact wandering saturation -/

open Set Function
open AreaDeficit.Surfaces
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]

/-- A compactly contained bad forward saturation admits one relatively
compact restricted source and an increasing finite puncture barrier whose
closure contains the original set.  This packages the topological reduction
needed before the finite-model area contradiction. -/
theorem exists_positiveArea_boundaryBarrier
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (O : TopologicalSpace.Opens X) (p : DiscCover O)
    (hsourceO : (f.source : Set X) ⊆ O)
    {A K : Set X} (hA : A ⊆ f.trapped \ f.omega)
    (hK : IsCompact K) (hKsource : K ⊆ f.source)
    (hsatK : f.saturation A ⊆ K) :
    ∃ (V : TopologicalSpace.Opens X)
      (hVsource : closure (V : Set X) ⊆ f.source) (P : ℕ → Finset X),
      K ⊆ V ∧ IsCompact (closure (V : Set X)) ∧ Monotone P ∧
      (∀ n x (hx : x ∈ V), x ∈ P n →
        f.map ⟨x, hVsource (subset_closure hx)⟩ ∈ P n) ∧
      A ⊆ (f.restrictSource V
        (subset_trans subset_closure hVsource)).trapped \
        (f.restrictSource V
          (subset_trans subset_closure hVsource)).omega ∧
      A ⊆ closure (⋃ n, ((P n : Finset X) : Set X)) := by
  obtain ⟨V, hVsource, P, hKV, hVcompact, hPmono, hPforward, hbad⟩ :=
    f.exists_boundaryBarrierFinsetPackage_in_subsurface
      hf O p hsourceO hK hKsource
  let hVs : (V : Set X) ⊆ f.source :=
    subset_trans subset_closure hVsource
  have hsatV : f.saturation A ⊆ V := hsatK.trans hKV
  have hArestrict :
      A ⊆ (f.restrictSource V hVs).trapped \ (f.restrictSource V hVs).omega :=
    f.subset_restrictSource_trapped_diff_omega_of_saturation_subset
      V hVs hA hsatV
  exact ⟨V, hVsource, P, hKV, hVcompact, hPmono, hPforward,
    hArestrict, hArestrict.trans hbad⟩

/-- If the compact saturation is a proper subset of the surface, delete a
coordinate disk away from it and run the boundary construction in the
resulting fixed hyperbolic subsurface.  This removes any hyperbolicity
assumption on the original ambient surface from the topological part of the
positive-area argument. -/
theorem exists_positiveArea_hyperbolicAnchor_boundaryBarrier
    [ConnectedSpace X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A K : Set X} (hA : A ⊆ f.trapped \ f.omega)
    (hK : IsCompact K) (hKne : K ≠ Set.univ)
    (hKsource : K ⊆ f.source) (hsatK : f.saturation A ⊆ K) :
    ∃ (D : RiemannDynamics.CoordDisk X)
      (_p : DiscCover D.compl)
      (W : TopologicalSpace.Opens X)
      (hW : (W : Set X) ⊆ f.source),
      let g := f.restrictSource W hW
      K ⊆ W ∧ g.saturation A = f.saturation A ∧
      ∃ (V : TopologicalSpace.Opens X)
        (hVsource : closure (V : Set X) ⊆ g.source)
        (P : ℕ → Finset X),
        K ⊆ V ∧ IsCompact (closure (V : Set X)) ∧ Monotone P ∧
        (∀ n x (hx : x ∈ V), x ∈ P n →
          g.map ⟨x, hVsource (subset_closure hx)⟩ ∈ P n) ∧
        A ⊆ (g.restrictSource V
          (subset_trans subset_closure hVsource)).trapped \
          (g.restrictSource V
            (subset_trans subset_closure hVsource)).omega ∧
        A ⊆ closure (⋃ n, ((P n : Finset X) : Set X)) := by
  obtain ⟨D, p, hKD⟩ :=
    exists_discCovered_coordDisk_compl_of_isClosed hK.isClosed hKne
  let W : TopologicalSpace.Opens X := f.source ⊓ D.compl
  let hW : (W : Set X) ⊆ f.source := fun _ hx => hx.1
  let g := f.restrictSource W hW
  have hKW : K ⊆ W := fun x hx => ⟨hKsource hx, hKD hx⟩
  have hsatW : f.saturation A ⊆ W := hsatK.trans hKW
  have hArestrict : A ⊆ g.trapped \ g.omega :=
    f.subset_restrictSource_trapped_diff_omega_of_saturation_subset
      W hW hA hsatW
  have hsateq : g.saturation A = f.saturation A :=
    f.restrictSource_saturation_eq_of_saturation_subset W hW
      (fun x hx => (hA hx).1) hsatW
  have hg : IsOpenHolomorphic g := f.isOpenHolomorphic_restrictSource hf W hW
  obtain ⟨V, hVsource, P, hKV, hVcompact, hPmono, hPforward,
      hAV, hAP⟩ :=
    g.exists_positiveArea_boundaryBarrier hg D.compl p
      (fun _ hx => hx.2) hArestrict hK hKW (hsateq.trans_le hsatK)
  exact ⟨D, p, W, hW, hKW, hsateq, V, hVsource, P, hKV,
    hVcompact, hPmono, hPforward, hAV, hAP⟩

end SurfaceDynamics.LocalMap
