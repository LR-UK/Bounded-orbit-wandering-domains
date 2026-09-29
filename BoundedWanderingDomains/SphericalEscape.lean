module

/- 
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.SphericalDerivedSet

@[expose] public section

/-!
# Spherical escape subsequences

The one-point compactification makes a planar sequence with unbounded
range accumulate at infinity. We extract a strictly increasing subsequence
converging to infinity in the spherical topology.
-/

open Set Filter OnePoint Topology RiemannDynamics

namespace BoundedWanderingDomains

/-- Every unbounded planar sequence has an increasing subsequence escaping
spherically to infinity. -/
theorem exists_subsequence_tendsto_infty_of_unbounded
    (u : ℕ → ℂ) (hu : ¬Bornology.IsBounded (Set.range u)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => ((u (φ n)) : OnePoint ℂ)) atTop (𝓝 ∞) := by
  have htail (N : ℕ) : ¬Bornology.IsBounded (u '' Set.Ici N) := by
    intro hb
    have hprefix : Bornology.IsBounded (u '' Set.Iio N) :=
      ((Set.finite_Iio N).image u).isBounded
    apply hu
    apply (hprefix.union hb).subset
    rintro z ⟨n, rfl⟩
    rcases lt_or_ge n N with h | h
    · exact Or.inl ⟨n, h, rfl⟩
    · exact Or.inr ⟨n, h, rfl⟩
  have hcluster : MapClusterPt (∞ : OnePoint ℂ) atTop
      (fun n => (u n : OnePoint ℂ)) := by
    apply mapClusterPt_atTop_iff_forall_mem_closure.mpr
    intro N
    have h := (infty_mem_sphericalDerivedSet_iff_mem_closure
      (u '' Set.Ici N)).mp ((infty_mem_sphericalDerivedSet_iff _).mpr (htail N))
    simpa only [Set.image_image, Function.comp_def] using h
  let : MetricSpace (OnePoint ℂ) := MetricSpace.ofDistTopology
    sphericalDist (fun x => (sphericalDist_eq_zero_iff x x).mpr rfl)
    sphericalDist_comm sphericalDist_triangle sphericalDist_induces_topology
    (fun x y hxy => (sphericalDist_eq_zero_iff x y).mp hxy)
  obtain ⟨φ, hφ, hlim⟩ := hcluster.tendsto_subseq
  exact ⟨φ, hφ, hlim⟩

end BoundedWanderingDomains
