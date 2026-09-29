module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.LocalDynamics

@[expose] public section

/-! # Surface singular values as the covering obstruction -/

open Set Function Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X]

/-- By the local definition of regular values, a local surface map is a
covering over the whole complement of its singular-value set. -/
theorem isCoveringMapOn_compl_singularValues (f : LocalMap X) :
    IsCoveringMapOn f.map f.singularValuesᶜ := by
  intro y hy
  have hy' : y ∈ f.regularValues := by
    simpa only [singularValues, compl_compl] using hy
  obtain ⟨W, _hW, hyW, _hrange, hcov⟩ := hy'
  exact hcov y hyW

/-- Restricting the source to the preimage of any set of regular values
produces a genuine covering of that target subtype. -/
theorem isCoveringMap_restrictPreimage_regular (f : LocalMap X)
    (S : Set X) (hS : S ⊆ f.regularValues) :
    IsCoveringMap (S.restrictPreimage f.map) := by
  apply IsCoveringMapOn.isCoveringMap_restrictPreimage
  exact f.isCoveringMapOn_compl_singularValues.mono (by
    simpa only [singularValues, compl_compl] using hS)

end SurfaceDynamics.LocalMap
