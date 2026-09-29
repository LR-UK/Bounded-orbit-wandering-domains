module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Sets.Opens

@[expose] public section

/-! # Countable compact inner sets for open target neighbourhoods -/

open Set Topology

namespace SurfaceDynamics

theorem exists_compact_inner_exhaustion
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
    (O : TopologicalSpace.Opens X) :
    ∃ L : ℕ → Set X, (∀ n, IsCompact (L n)) ∧ (∀ n, L n ⊆ O) ∧
      ∀ x ∈ O, ∃ n, x ∈ interior (L n) := by
  let locallyCompactOpen : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  let K := CompactExhaustion.choice O
  refine ⟨fun n => Subtype.val '' K n,
    fun n => (K.isCompact n).image continuous_subtype_val, ?_, ?_⟩
  · rintro n x ⟨y, _, rfl⟩
    exact y.2
  · intro x hx
    obtain ⟨n, hn⟩ := K.exists_mem ⟨x, hx⟩
    have hneigh : Subtype.val '' interior (K (n + 1)) ∈ 𝓝 x :=
      (O.isOpen.isOpenMap_subtype_val _ isOpen_interior).mem_nhds
        ⟨⟨x, hx⟩, K.subset_interior_succ n hn, rfl⟩
    exact ⟨n + 1, mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset hneigh (image_mono interior_subset))⟩

end SurfaceDynamics
