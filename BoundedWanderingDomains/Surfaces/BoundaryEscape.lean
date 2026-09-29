module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import Mathlib.Geometry.Manifold.Complex
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

/-! # Escape toward a deleted point

A curve in an open part of a compact surface which converges in the compact
surface to a deleted boundary point escapes every compact subset of the open
surface.  This is the topological bridge needed to apply the old-end metric
comparison to coordinate puncture charts. -/

open Set Filter TopologicalSpace
open scoped Topology

namespace AreaDeficit.Surfaces

theorem tendsto_cocompact_openSubtype_of_tendsto_boundary
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TopologicalSpace ι] {l : Filter ι} (O : Opens X) {a : X}
    (ha : a ∉ O) (x : ι → O)
    (hx : Tendsto (fun i => (x i : X)) l (𝓝 a)) :
    Tendsto x l (cocompact O) := by
  rw [hasBasis_cocompact.tendsto_right_iff]
  intro K hK
  have hKi : IsCompact ((Subtype.val : O → X) '' K) :=
    hK.image continuous_subtype_val
  have haK : a ∉ (Subtype.val : O → X) '' K := by
    rintro ⟨y, _, rfl⟩
    exact ha y.property
  have hnhds : ((Subtype.val : O → X) '' K)ᶜ ∈ 𝓝 a :=
    hKi.isClosed.isOpen_compl.mem_nhds haK
  filter_upwards [hx.eventually hnhds] with i hi
  intro hxi
  exact hi ⟨x i, hxi, rfl⟩

end AreaDeficit.Surfaces
