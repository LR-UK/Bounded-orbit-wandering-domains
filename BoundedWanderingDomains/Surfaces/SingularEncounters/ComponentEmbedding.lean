module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Maps.Basic

@[expose] public section

/-! # Connected components under an embedding -/

open Set Topology

namespace SurfaceDynamics

theorem embedding_image_connectedComponentIn
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {e : A → B} (he : IsEmbedding e) (S : Set A) {a : A} (ha : a ∈ S) :
    e '' connectedComponentIn S a = connectedComponentIn (e '' S) (e a) := by
  apply (he.continuous.continuousOn.image_connectedComponentIn_subset ha).antisymm
  let C := connectedComponentIn (e '' S) (e a)
  have hCrange : C ⊆ range e :=
    (connectedComponentIn_subset _ _).trans (image_subset_range _ _)
  have himage : e '' (e ⁻¹' C) = C := image_preimage_eq_of_subset hCrange
  have hconn : IsPreconnected (e ⁻¹' C) := by
    apply he.isPreconnected_image.mp
    rw [himage]
    exact isPreconnected_connectedComponentIn
  have hpre : e ⁻¹' C ⊆ S := by
    intro u hu
    obtain ⟨v, hv, hvu⟩ := connectedComponentIn_subset _ _ hu
    exact he.injective hvu ▸ hv
  have hsub := hconn.subset_connectedComponentIn
    (mem_connectedComponentIn (mem_image_of_mem e ha)) hpre
  intro b hb
  obtain ⟨u, hu⟩ := hCrange hb
  have huC : u ∈ e ⁻¹' C := by
    change e u ∈ C
    rwa [hu]
  exact ⟨u, hsub huC, hu⟩

end SurfaceDynamics
