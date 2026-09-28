/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.FiniteFibers
import BoundedWanderingDomains.Surfaces.LocalCompactAreaAdvance

/-! # Local compact models separated from their boundary images -/

open Set Function Topology
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [LocallyCompactSpace X] [T2Space X]
  [DecidableEq X]

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [DecidableEq X] in
/-- Every source point has a compact source model and a compact target
neighbourhood separated from the image of the model boundary. -/
theorem exists_local_compact_model_patch (f : LocalMap X)
    (hf : IsOpenHolomorphic f) (V : TopologicalSpace.Opens X)
    (x : f.source) (hxV : (x : X) ∈ V) :
    ∃ (K L N : Set X), IsCompact K ∧ K ⊆ f.source ∧ IsCompact L ∧
      K ⊆ V ∧ IsOpen N ∧ (x : X) ∈ N ∧ N ⊆ interior K ∧
      f.totalize '' N ⊆ L ∧
      Disjoint L (f.map '' frontier (f.sourceCompact K)) := by
  have hdisc := isDiscrete_fiber_of_isOpenMap_of_mdifferentiable
    hf.1 hf.2 (f.map x)
  rw [isDiscrete_iff_forall_mem_exists_isOpen] at hdisc
  obtain ⟨O, hOopen, hOfiber⟩ := hdisc x rfl
  let Oa : Set X := (Subtype.val '' O) ∩ V
  have hOaopen : IsOpen Oa :=
    (f.source.isOpen.isOpenMap_subtype_val O hOopen).inter V.isOpen
  have hxOa : (x : X) ∈ Oa := ⟨⟨x, by
    have : x ∈ O ∩ {z | f.map z = f.map x} := hOfiber.symm ▸ Set.mem_singleton x
    exact this.1, rfl⟩, hxV⟩
  obtain ⟨K, hK, hxK, hKO⟩ := exists_compact_subset hOaopen hxOa
  have hKsource : K ⊆ f.source := by
    rintro z hz
    obtain ⟨⟨w, -, rfl⟩, -⟩ := hKO hz
    exact w.property
  have hKV : K ⊆ V := fun _ hz => (hKO hz).2
  let H : Set X := f.map '' frontier (f.sourceCompact K)
  have hKs : IsCompact (f.sourceCompact K) :=
    f.sourceCompact_isCompact hK hKsource
  have hH : IsCompact H := by
    apply (hKs.of_isClosed_subset isClosed_frontier ?_).image hf.2.continuous
    simpa only [hKs.isClosed.closure_eq] using
      (frontier_subset_closure : frontier (f.sourceCompact K) ⊆ _)
  have hfxH : f.map x ∉ H := by
    rintro ⟨z, hzfront, hzx⟩
    have hzK : z ∈ f.sourceCompact K := by
      exact hKs.isClosed.frontier_subset hzfront
    have hzOa : (z : X) ∈ Oa := hKO hzK
    obtain ⟨⟨w, hwO, hwz⟩, -⟩ := hzOa
    have hw_eq : w = z := Subtype.ext hwz
    subst w
    have hzfiber : z ∈ {w | f.map w = f.map x} := hzx
    have hzx' : z = x := Set.mem_singleton_iff.mp
      (hOfiber ▸ ⟨hwO, hzfiber⟩)
    subst z
    have hxint : x ∈ interior (f.sourceCompact K) := by
      apply preimage_interior_subset_interior_preimage continuous_subtype_val
      exact hxK
    rw [frontier, hKs.isClosed.closure_eq] at hzfront
    exact hzfront.2 hxint
  obtain ⟨L, hL, hfxL, hLH⟩ :=
    exists_compact_subset hH.isClosed.isOpen_compl hfxH
  let Ns : Set f.source := f.map ⁻¹' interior L
  let N : Set X := Subtype.val '' Ns ∩ interior K
  have hNopen : IsOpen N :=
    (f.source.isOpen.isOpenMap_subtype_val Ns
      (isOpen_interior.preimage hf.2.continuous)).inter isOpen_interior
  have hxN : (x : X) ∈ N := ⟨⟨x, hfxL, rfl⟩, hxK⟩
  refine ⟨K, L, N, hK, hKsource, hL, hKV, hNopen, hxN,
    inter_subset_right, ?_, ?_⟩
  · rintro y ⟨z, ⟨⟨w, hw, hwz⟩, -⟩, rfl⟩
    subst z
    rw [f.totalize_eq w.property]
    exact interior_subset hw
  · exact Set.disjoint_left.mpr fun y hyL hyH => hLH hyL hyH

end SurfaceDynamics.LocalMap
