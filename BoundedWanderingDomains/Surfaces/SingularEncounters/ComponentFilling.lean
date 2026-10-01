module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.RestrictedCompletion
public import BoundedWanderingDomains.Surfaces.BKL.ShrinkingFillings

@[expose] public section

/-! # Filling over a disc regular for a source restriction

Regularity is required only for the restriction to the visited open set V.
No regularity of the other inverse components is assumed.
-/

open Set Function Metric Topology
open scoped Manifold
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

theorem projected_fill_subset_denseCompletion_of_restricted_regular_puncturedDisc
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (q : DiscCovering X)
    (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source)
    {t : unitDisc → X} (ht : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) t) (hte : IsOpenEmbedding t)
    (hreg : ∀ z : puncturedUnitDisc,
      t ⟨z, z.2.1⟩ ∈ (f.restrictSource V hV).regularValues)
    {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K) (hKD : K ⊆ ball 0 1)
    (hsource : ∀ z ∈ K, ∀ hzd : z ∈ ball 0 1, q.projection ⟨z, hzd⟩ ∈ V)
    (himage : ∀ z ∈ K, ∀ hzd : z ∈ ball 0 1,
      f.totalize (q.projection ⟨z, hzd⟩) ∈
        range (fun w : puncturedUnitDisc => t ⟨w, w.2.1⟩)) :
    ComplexApproximation.fill K ⊆ ball 0 1 ∧
      ∀ z ∈ ComplexApproximation.fill K, ∀ hzd : z ∈ ball 0 1,
        q.projection ⟨z, hzd⟩ ∈ f.denseCompletionSource := by
  let g := f.restrictSource V hV
  have hg := f.isOpenHolomorphic_restrictSource hf V hV
  obtain ⟨hfill, hsrc⟩ := projected_fill_subset_denseCompletion_of_regular_puncturedDisc
    g hg q ht hte hreg hK hKc hKD hsource (by
      intro z hz hzd
      have hs := hsource z hz hzd
      rw [g.totalize_eq hs]
      change f.map ⟨q.projection ⟨z, hzd⟩, hV hs⟩ ∈ _
      rw [← f.totalize_eq (hV hs)]
      exact himage z hz hzd)
  refine ⟨hfill, fun z hz hzd => ?_⟩
  exact f.denseCompletionSource_restrictSource_subset hf.2 V hV (hsrc z hz hzd)

/-- Componentwise punctured-disc filling, including the exceptional-value
control needed when recovering the original wandering components. -/
theorem compactFill_restricted_source_and_added_images
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    [NoncompactComponents X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (q : ComponentwiseDiscCover X)
    (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source)
    (D : RiemannDynamics.CoordDisk X)
    (hreg : ∀ z : puncturedUnitDisc,
      D.param ⟨z, z.2.1⟩ ∈ (f.restrictSource V hV).regularValues)
    {E : Set X} (hS : (f.restrictSource V hV).singularValues ∩ D.closedCarrier ⊆ E)
    {K : Set X} (hK : IsCompact K) (hKc : IsConnected K) (hKV : K ⊆ V)
    (himage : MapsTo f.totalize K
      (range (fun w : puncturedUnitDisc => D.param ⟨w, w.2.1⟩)))
    (W : TopologicalSpace.Opens X) [SimplyConnectedSpace W]
    (hKW : compactFill K ⊆ W) :
    compactFill K ⊆ f.denseCompletion.source ∧
      ∀ x ∈ compactFill K, x ∉ f.source → f.denseCompletion.totalize x ∈ E := by
  let g := f.restrictSource V hV
  have hg := f.isOpenHolomorphic_restrictSource hf V hV
  have hfillg : compactFill K ⊆ g.denseCompletionSource :=
    compactFill_subset_denseCompletion_in_simplyConnected_neighborhood g hg q
      D.mdifferentiable_param D.isOpenEmbedding_param hreg hK hKc hKV (by
        intro x hx
        rw [g.totalize_eq (hKV hx)]
        change f.map ⟨x, hV (hKV hx)⟩ ∈ _
        rw [← f.totalize_eq (hV (hKV hx))]
        exact himage hx)
      W hKW
  have hfill : compactFill K ⊆ f.denseCompletion.source :=
    hfillg.trans (f.denseCompletionSource_restrictSource_subset hf.2 V hV)
  have hmap : MapsTo f.denseCompletion.totalize K D.closedCarrier := by
    intro x hx
    rw [f.denseCompletion_totalize_eq hf.2 (hV (hKV hx))]
    obtain ⟨w, hw⟩ := himage hx
    exact hw ▸ D.param_mem_closedCarrier ⟨w, w.2.1⟩
  have hmapfill := f.denseCompletion.mapsTo_compactFill_of_forward
    (f.isOpenHolomorphic_denseCompletion hf) hK.isClosed hfill hmap
  refine ⟨hfill, fun x hx hxo => ?_⟩
  rw [f.denseCompletion.totalize_eq (hfill hx)]
  apply f.denseCompletionValue_mem_of_restricted_added hf V hV hS (hfillg hx) hxo
  have hd := compactFill_subset_coordDisk_of_noncompactComponents D (Subset.refl D.closedCarrier) (hmapfill hx)
  rwa [f.denseCompletion.totalize_eq (hfill hx)] at hd

end SurfaceDynamics.BKL
