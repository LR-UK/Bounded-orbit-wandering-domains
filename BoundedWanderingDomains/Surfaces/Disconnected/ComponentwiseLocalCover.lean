module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseCover

@[expose] public section

/-! # Hyperbolicity inherited by a locally biholomorphic source -/

open Set Function TopologicalSpace
open scoped Manifold

namespace AreaDeficit.Surfaces.ComponentwiseDiscCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X]

theorem nonempty_of_holomorphic_localHomeomorph (p : ComponentwiseDiscCover X)
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (f : M → X) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hfloc : IsLocalHomeomorph f) : Nonempty (DiscCover M) := by
  classical
  let x : M := Classical.choice (inferInstance : Nonempty M)
  let c := ConnectedComponents.mk (f x)
  have hfc : ∀ y, f y ∈ ambientComponent c := by
    intro y
    change f y ∈ (ambientComponent c : Set X)
    rw [show (ambientComponent c : Set X) = connectedComponent (f x) from ambientComponent_mk (f x)]
    exact (isPreconnected_range hf.continuous).subset_connectedComponent
      (mem_range_self x) (mem_range_self y)
  let g : M → ambientComponent c := fun y => ⟨f y, hfc y⟩
  have hg : Continuous g := hf.continuous.subtype_mk hfc
  have hgh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g :=
    (mdifferentiable_subtypeVal_comp_iff (ambientComponent c) g).mp hf
  have hgloc : IsLocalHomeomorph g :=
    (show IsLocalHomeomorph ((Subtype.val : ambientComponent c → X) ∘ g) from hfloc).of_comp
      (ambientComponent c).isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph hg
  exact (p.cover c).nonempty_of_holomorphic_localHomeomorph g hgh hgloc

noncomputable def pullback (p : ComponentwiseDiscCover X)
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]
    (f : M → X) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hfloc : IsLocalHomeomorph f) : ComponentwiseDiscCover M where
  cover c := Classical.choice (p.nonempty_of_holomorphic_localHomeomorph
    (f ∘ (Subtype.val : ambientComponent c → M))
    (hf.comp (mdifferentiable_subtype_val (ambientComponent c)))
    (hfloc.comp (ambientComponent c).isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph))

variable [T2Space X] [SecondCountableTopology X]

noncomputable def restrict (p : ComponentwiseDiscCover X) (U : Opens X) :
    ComponentwiseDiscCover U where
  cover c := Classical.choice (p.nonempty_of_holomorphic_localHomeomorph
    ((Subtype.val : U → X) ∘ (Subtype.val : ambientComponent c → U))
    ((mdifferentiable_subtype_val U).comp (mdifferentiable_subtype_val (ambientComponent c)))
    (U.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph.comp
      (ambientComponent c).isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph))

end AreaDeficit.Surfaces.ComponentwiseDiscCover
