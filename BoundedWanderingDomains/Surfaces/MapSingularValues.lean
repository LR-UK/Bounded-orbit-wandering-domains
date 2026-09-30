module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import Mathlib.Topology.Covering.Basic

@[expose] public section

/-! # Singular values of maps between different spaces

Regularity allows an evenly covered neighbourhood with no sheets. In particular,
points outside the closure of the image are regular. An empty fibre alone does
not imply regularity: omitted asymptotic values are still singular.
-/

open Set Topology

namespace SurfaceDynamics.Map

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]

/-- A regular value has a neighbourhood over which the map is a covering;
the covering is allowed to have no sheets. -/
def regularValues (g : A → B) : Set B :=
  {y | ∃ V : Set B, IsOpen V ∧ y ∈ V ∧ IsCoveringMapOn g V}

/-- Singular values are the obstruction to locally being a covering. -/
def singularValues (g : A → B) : Set B := (regularValues g)ᶜ

theorem singularValues_subset_closure_range (g : A → B) :
    singularValues g ⊆ closure (range g) := by
  intro y hy
  by_contra hn
  apply hy
  refine ⟨(closure (range g))ᶜ, isClosed_closure.isOpen_compl, hn, ?_⟩
  intro z hz
  exact (IsEvenlyCovered.of_preimage_eq_empty (f := g) Empty
    (isClosed_closure.isOpen_compl.mem_nhds hz)
    (Set.eq_empty_of_forall_notMem fun a ha => ha (subset_closure (mem_range_self a)))).to_isEvenlyCovered_preimage

/-- A regular value which is approached by image points has a preimage. -/
theorem mem_range_of_regular_of_mem_closure (g : A → B) {y : B}
    (hr : y ∈ regularValues g) (hc : y ∈ closure (range g)) : y ∈ range g := by
  obtain ⟨V, _, hyV, hcov⟩ := hr
  obtain ⟨_, W, hyW, hW, _, e, _⟩ := hcov y hyV
  obtain ⟨b, hbW, hb⟩ := mem_closure_iff.mp hc W hW hyW
  obtain ⟨a, rfl⟩ := hb
  exact ⟨(e ⟨a, hbW⟩).2, (e ⟨a, hbW⟩).2.property⟩

end SurfaceDynamics.Map
