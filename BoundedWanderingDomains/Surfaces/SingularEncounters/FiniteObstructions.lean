module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.LocalDynamics
public import BoundedWanderingDomains.Surfaces.BKL.ComponentRecovery
public import BoundedWanderingDomains.Surfaces.SingularEncounters.InverseComponents
public import Mathlib.Topology.Connected.Clopen

@[expose] public section

/-! # Genuine obstructions control the whole punctured target

If only exceptional values obstruct a restriction at points in the closure of
its image, connectedness forces the entire remaining target into its image.
This prevents omitted open regions from being mistaken for encountered
singular values.
-/

open Set Function Filter Topology
open scoped Manifold

namespace SurfaceDynamics.BKL

theorem isConnected_diff_finite
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [ChartedSpace ℂ X] (D : TopologicalSpace.Opens X) (hD : IsConnected (D : Set X))
    {E : Set X} (hE : E.Finite) (hne : ((D : Set X) \ E).Nonempty) :
    IsConnected ((D : Set X) \ E) := by
  apply (isOpen_isConnected_diff_of_locally_isolated D hD ?_ hne).2
  intro x _
  have hc : IsClosed (E \ {x}) := hE.sdiff.isClosed
  filter_upwards [hc.isOpen_compl.mem_nhds (by simp)] with y hy hyE
  by_contra hne
  exact hy ⟨hyE, hne⟩

end SurfaceDynamics.BKL

namespace SurfaceDynamics.LocalMap

theorem regularValues_of_image_obstructions
    {X : Type*} [TopologicalSpace X] (f : LocalMap X) (hopen : IsOpenMap f.map)
    {D E : Set X} (hconn : IsPreconnected (D \ E))
    (hne : (range f.map ∩ (D \ E)).Nonempty)
    (hobs : f.singularValues ∩ closure (range f.map) ∩ D ⊆ E) :
    D \ E ⊆ f.regularValues := by
  let A := D \ E
  let : PreconnectedSpace A := Subtype.preconnectedSpace hconn
  have hreg : closure (range f.map) ∩ A ⊆ f.regularValues := by
    intro y hy
    by_contra hn
    exact hy.2.2 (hobs ⟨⟨hn, hy.1⟩, hy.2.1⟩)
  have hmem : closure (range f.map) ∩ A ⊆ range f.map := by
    intro y hy
    obtain ⟨W, _, hyW, hW, _⟩ := hreg hy
    exact hW hyW
  let B : Set A := Subtype.val ⁻¹' range f.map
  have hBo : IsOpen B := by
    have hr : IsOpen (range f.map) := by simpa only [image_univ] using hopen univ isOpen_univ
    exact hr.preimage continuous_subtype_val
  have hBeq : B = Subtype.val ⁻¹' closure (range f.map) := by
    ext y
    exact ⟨fun hy => subset_closure hy, fun hy => hmem ⟨hy, y.2⟩⟩
  have hBc : IsClosed B := by
    rw [hBeq]
    exact isClosed_closure.preimage continuous_subtype_val
  have hBne : B.Nonempty := by
    obtain ⟨y, hyR, hyA⟩ := hne
    exact ⟨⟨y, hyA⟩, hyR⟩
  have hBu : B = univ := (show IsClopen B from ⟨hBc, hBo⟩).eq_univ hBne
  intro y hy
  have hyB : (⟨y, hy⟩ : A) ∈ B := hBu.symm ▸ mem_univ _
  exact hreg ⟨subset_closure hyB, hy⟩

theorem inverseComponent_regularValues_of_finite_obstructions
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (D : TopologicalSpace.Opens X) (hD : IsConnected (D : Set X))
    {E : Set X} (hE : E.Finite) (a : f.source) (haD : f.map a ∈ D) (haE : f.map a ∉ E)
    (hobs : f.componentSingularValues hf.2.continuous D a ⊆ E) :
    (D : Set X) \ E ⊆ (f.inverseComponentMap hf.2.continuous D a).regularValues := by
  have hVa : (a : X) ∈ f.inverseComponentSource hf.2.continuous D a :=
    ⟨a, mem_connectedComponentIn haD, rfl⟩
  have hnon : (range (f.inverseComponentMap hf.2.continuous D a).map ∩
      ((D : Set X) \ E)).Nonempty :=
    ⟨f.map a, ⟨⟨a, hVa⟩, rfl⟩, haD, haE⟩
  exact (f.inverseComponentMap hf.2.continuous D a).regularValues_of_image_obstructions
    (f.isOpenHolomorphic_restrictSource hf _ (f.inverseComponentSource_subset _ D a)).1
    (BKL.isConnected_diff_finite D hD hE ⟨f.map a, haD, haE⟩).isPreconnected hnon hobs

end SurfaceDynamics.LocalMap
