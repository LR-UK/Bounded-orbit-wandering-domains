module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.LocalMapSubsurface
public import BoundedWanderingDomains.Surfaces.LocalMapTotalization

@[expose] public section

/-! # Totalized trapped orbits commute with source and ambient restrictions -/

open Set Function

namespace SurfaceDynamics.LocalMap

theorem totalize_iterate_restrictAmbient_restrictSource
    {X : Type*} [TopologicalSpace X] (f : LocalMap X)
    (O V : TopologicalSpace.Opens X) (hVs : (V : Set X) ⊆ f.source)
    (hVO : (V : Set X) ⊆ O)
    (hm : ∀ x : (f.restrictSource V hVs).source, (f.restrictSource V hVs).map x ∈ O)
    (y : O) (hy : y ∈ ((f.restrictSource V hVs).restrictAmbient O hVO hm).trapped)
    (n : ℕ) :
    ((((f.restrictSource V hVs).restrictAmbient O hVO hm).totalize^[n]) y : X) =
      (f.totalize^[n]) (y : X) := by
  let g := (f.restrictSource V hVs).restrictAmbient O hVO hm
  change ((g.totalize^[n]) y : X) = (f.totalize^[n]) (y : X)
  induction n with
  | zero => rfl
  | succ n ih =>
    have hgn : (g.totalize^[n]) y ∈ g.source := by
      rw [g.totalize_iterate_orbit n ⟨y, hy⟩]
      exact g.orbit_mem_source n ⟨y, hy⟩
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (g.totalize ((g.totalize^[n]) y) : X) =
      f.totalize ((f.totalize^[n]) (y : X))
    rw [← ih, g.totalize_eq hgn, f.totalize_eq (hVs hgn)]
    rfl

end SurfaceDynamics.LocalMap
