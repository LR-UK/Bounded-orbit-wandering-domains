/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactInteriorCover
import BoundedWanderingDomains.Surfaces.LocalMapTotalization

/-! # Compact covering models for an open-source local map -/

open Set Function Topology
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [LocallyCompactSpace X] [T2Space X]
  [DecidableEq X]

/-- A compact ambient set, regarded inside the open source of a local map. -/
def sourceCompact (f : LocalMap X) (K : Set X) : Set f.source :=
  (Subtype.val : f.source → X) ⁻¹' K

theorem sourceCompact_isCompact (f : LocalMap X) {K : Set X}
    (hK : IsCompact K) (hKsource : K ⊆ f.source) :
    IsCompact (f.sourceCompact K) := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  change IsCompact ((Subtype.val : f.source → X) ''
    ((Subtype.val : f.source → X) ⁻¹' K))
  rw [image_preimage_eq_inter_range]
  convert hK using 1
  exact inter_eq_left.mpr (fun x hx => ⟨⟨x, hKsource hx⟩, rfl⟩)

/-- The ambient open domain corresponding to the interior of a compact
covering model constructed inside the local map's open source. -/
def localCompactCoverDomain (f : LocalMap X) (K : Set X)
    (S : TopologicalSpace.Opens X) (hf : Continuous f.map) :
    TopologicalSpace.Opens X := by
  let Ks := f.sourceCompact K
  let W := compactCoverDomain Ks S f.map hf
  exact ⟨(Subtype.val : f.source → X) '' (W : Set f.source),
    f.source.isOpen.isOpenMap_subtype_val (W : Set f.source) W.isOpen⟩

/-- The local compact-cover domain is canonically homeomorphic to the
nested subtype domain on which `compact_interior_isCoveringMap` is stated. -/
noncomputable def localCompactCoverDomainHomeomorph (f : LocalMap X)
    (K : Set X) (S : TopologicalSpace.Opens X) (hf : Continuous f.map) :
    compactCoverDomain (f.sourceCompact K) S f.map hf ≃ₜ
      f.localCompactCoverDomain K S hf :=
  by
    unfold localCompactCoverDomain
    exact (show IsEmbedding (Subtype.val : f.source → X) from
      IsEmbedding.subtypeVal).homeomorphImage
        (compactCoverDomain (f.sourceCompact K) S f.map hf : Set f.source)

/-- A point in the ambient interior of the compact source model whose image
lies in the target open set belongs to the ambient compact-cover domain. -/
theorem mem_localCompactCoverDomain_of_mem_interior
    (f : LocalMap X) {K : Set X} (S : TopologicalSpace.Opens X)
    (hf : Continuous f.map) (hKsource : K ⊆ f.source) {x : X}
    (hxK : x ∈ interior K)
    (hfx : f.map ⟨x, hKsource (interior_subset hxK)⟩ ∈ S) :
    x ∈ f.localCompactCoverDomain K S hf := by
  let xs : f.source := ⟨x, hKsource (interior_subset hxK)⟩
  have hxsint : xs ∈ interior (f.sourceCompact K) := by
    apply preimage_interior_subset_interior_preimage continuous_subtype_val
    exact hxK
  refine ⟨xs, ⟨hxsint, ?_⟩, rfl⟩
  change f.map xs ∈ S
  simpa only [xs] using hfx

/-- Away from finitely many branch values and the compact image of the
source boundary, a local holomorphic map is a covering between ambient open
surface domains.  This is the precise bridge needed by the area-advance
argument: the resulting map agrees with the harmless ambient totalisation. -/
theorem exists_finite_branch_values_local_compact_covering
    (f : LocalMap X) (hf : IsOpenHolomorphic f) {K : Set X}
    (hK : IsCompact K) (hKsource : K ⊆ f.source) :
    ∃ (E : Finset X),
      IsCompact (f.map '' frontier (f.sourceCompact K)) ∧
      ∀ (S : TopologicalSpace.Opens X),
        (S : Set X) ⊆ (E : Set X)ᶜ →
        (S : Set X) ⊆ (f.map '' frontier (f.sourceCompact K))ᶜ →
        ∃ F : f.localCompactCoverDomain K S hf.2.continuous → S,
          MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧ IsCoveringMap F ∧
          (fun x : f.localCompactCoverDomain K S hf.2.continuous =>
            f.totalize x) = (fun x => (F x : X)) := by
  letI : LocallyCompactSpace f.source := f.source.isOpen.locallyCompactSpace
  let Ks := f.sourceCompact K
  have hKs : IsCompact Ks := f.sourceCompact_isCompact hK hKsource
  obtain ⟨E, hE⟩ :=
    exists_finite_branch_values_compact_covering hf.2 hf.1 hKs
  let H : Set X := f.map '' frontier Ks
  have hfront : IsCompact (frontier Ks) := by
    apply hKs.of_isClosed_subset isClosed_frontier
    simpa only [hKs.isClosed.closure_eq] using (frontier_subset_closure : frontier Ks ⊆ closure Ks)
  have hH : IsCompact H := hfront.image hf.2.continuous
  refine ⟨E, hH, ?_⟩
  intro S hSE hSH
  have hint : ∀ z ∈ Ks, f.map z ∈ S → z ∈ interior Ks := by
    intro z hzK hfzS
    by_contra hzint
    have hzfront : z ∈ frontier Ks := by
      rw [frontier, hKs.isClosed.closure_eq]
      exact ⟨hzK, hzint⟩
    exact hSH hfzS ⟨z, hzfront, rfl⟩
  have hcovK : IsCoveringMapOn (fun z : Ks => f.map z) S :=
    hE S hSE hint
  have hcovW : IsCoveringMap
      (fun z : compactCoverDomain Ks S f.map hf.2.continuous =>
        (⟨f.map z, z.2.2⟩ : S)) :=
    compact_interior_isCoveringMap S hKs hf.2.continuous hint hcovK
  let e := f.localCompactCoverDomainHomeomorph K S hf.2.continuous
  let F : f.localCompactCoverDomain K S hf.2.continuous → S :=
    (fun z : compactCoverDomain Ks S f.map hf.2.continuous =>
      (⟨f.map z, z.2.2⟩ : S)) ∘ e.symm
  have hcovF : IsCoveringMap F := hcovW.comp_homeomorph e.symm
  have hdiffW : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun z : compactCoverDomain Ks S f.map hf.2.continuous =>
        (⟨f.map z, z.2.2⟩ : S)) := by
    apply (AreaDeficit.Surfaces.mdifferentiable_subtypeVal_comp_iff S _).mp
    exact hf.2.comp (AreaDeficit.Surfaces.mdifferentiable_subtype_val _)
  have hediff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e.symm := by
    let W := compactCoverDomain Ks S f.map hf.2.continuous
    apply (AreaDeficit.Surfaces.mdifferentiable_subtypeVal_comp_iff W e.symm).mp
    apply (AreaDeficit.Surfaces.mdifferentiable_subtypeVal_comp_iff f.source
      ((Subtype.val : W → f.source) ∘ e.symm)).mp
    have heq : (Subtype.val : f.source → X) ∘
        (Subtype.val : W → f.source) ∘ e.symm =
        (Subtype.val : f.localCompactCoverDomain K S hf.2.continuous → X) := by
      funext x
      have hx := congrArg
        (fun y : f.localCompactCoverDomain K S hf.2.continuous => (y : X))
        (e.apply_symm_apply x)
      change (((e.symm x : W) : f.source) : X) = (x : X) at hx
      exact hx
    rw [heq]
    exact AreaDeficit.Surfaces.mdifferentiable_subtype_val _
  have hdiffF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F :=
    hdiffW.comp hediff
  refine ⟨F, hdiffF, hcovF, ?_⟩
  funext x
  have hxsource : (x : X) ∈ f.source := by
    obtain ⟨w, hw, heq⟩ := x.property
    exact heq ▸ w.property
  rw [f.totalize_eq hxsource]
  change f.map ⟨(x : X), hxsource⟩ = f.map (e.symm x : f.source)
  congr 1
  apply Subtype.ext
  have hx := congrArg
    (fun y : f.localCompactCoverDomain K S hf.2.continuous => (y : X))
    (e.apply_symm_apply x)
  change (((e.symm x : compactCoverDomain Ks S f.map hf.2.continuous) :
    f.source) : X) = (x : X) at hx
  exact hx.symm

end SurfaceDynamics.LocalMap
