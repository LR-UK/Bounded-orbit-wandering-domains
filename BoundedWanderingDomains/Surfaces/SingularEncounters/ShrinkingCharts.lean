module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.CoordinateDiscParam
public import Mathlib.Order.Filter.CountablyGenerated

@[expose] public section

/-! # Shrinking analytic coordinate neighborhoods at a prescribed point -/

open Set Filter Topology

namespace SurfaceDynamics

theorem exists_shrinking_coordDisks
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    [FirstCountableTopology X] (x : X) :
    ∃ Q : ℕ → RiemannDynamics.CoordDisk X,
      (∀ n, (Q n).center = x) ∧
      ∀ O ∈ 𝓝 x, ∀ᶠ n in atTop, (Q n).closedCarrier ⊆ O := by
  obtain ⟨V, hV, hb⟩ := (nhds_basis_opens x).exists_antitone_subbasis
  choose Q hQ hQV using fun n =>
    exists_coordDisk_center_closedCarrier_subset (hV n).2 (hV n).1
  refine ⟨Q, hQ, ?_⟩
  intro O hO
  obtain ⟨n, _, hn⟩ := hb.toHasBasis.mem_iff.mp hO
  filter_upwards [eventually_ge_atTop n] with m hm
  exact (hQV m).trans ((hb.antitone hm).trans hn)

end SurfaceDynamics
