module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.DiscCover
public import BoundedWanderingDomains.Surfaces.SubtypeHolomorphic

@[expose] public section

/-! # A disc cover on the top open subtype -/

open Set Function
open scoped Manifold

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X]

/-- Regard a disc cover of a surface as a disc cover of its top open
subtype. -/
noncomputable def DiscCover.top (p : DiscCover X) :
    DiscCover (⊤ : TopologicalSpace.Opens X) where
  projection := fun z => ⟨p.projection z, trivial⟩
  holomorphic := by
    apply (mdifferentiable_subtypeVal_comp_iff
      (⊤ : TopologicalSpace.Opens X) _).mp
    exact p.holomorphic
  covering := by
    let e : X ≃ₜ (⊤ : TopologicalSpace.Opens X) :=
      (Homeomorph.Set.univ X).symm
    change IsCoveringMap (e ∘ p.projection)
    exact p.covering.homeomorph_comp e
  surjective := by
    intro x
    obtain ⟨z, hz⟩ := p.surjective (x : X)
    exact ⟨z, Subtype.ext hz⟩

end AreaDeficit.Surfaces
