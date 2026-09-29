module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SubsurfaceRegularValues
public import BoundedWanderingDomains.Surfaces.AnchorComplementModels
public import BoundedWanderingDomains.Surfaces.SaturationDynamics

@[expose] public section

/-! # Regular source pieces after removing finitely many ambient points -/

open Set Function Topology
open AreaDeficit.Surfaces
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X]

theorem regular_piece_on_anchor_complement
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (F E : Finset X)
    (hFE : f.totalize '' (F : Set X) ⊆ (E : Set X))
    (V : TopologicalSpace.Opens X) (hVs : (V : Set X) ⊆ f.source)
    (hVO : (V : Set X) ⊆ anchorComplement F)
    (hm : ∀ x : (f.restrictSource V hVs).source,
      (f.restrictSource V hVs).map x ∈ anchorComplement F)
    (hfull : ∀ x : f.source, (x : X) ∈ anchorComplement F →
      f.map x ∈ anchorComplement F → (x : X) ∈ V)
    (T D : TopologicalSpace.Opens X) (hTs : (T : Set X) ⊆ f.source)
    (hreg : (D : Set X) \ (E : Set X) ⊆ (f.restrictSource T hTs).regularValues) :
    let O := anchorComplement F
    let g := (f.restrictSource V hVs).restrictAmbient O hVO hm
    let TO : TopologicalSpace.Opens O :=
      ⟨Subtype.val ⁻¹' ((V ⊓ T : TopologicalSpace.Opens X) : Set X),
        (V ⊓ T).isOpen.preimage continuous_subtype_val⟩
    ∃ hTO : (TO : Set O) ⊆ g.source,
      (Subtype.val ⁻¹' (D : Set X)) \ (finiteStageOnAnchorComplement F E : Set O) ⊆
        (g.restrictSource TO hTO).regularValues := by
  classical
  dsimp only
  let O := anchorComplement F
  let r := f.restrictSource T hTs
  let Z := V ⊓ T
  have hZr : (Z : Set X) ⊆ r.source := fun _ hx => hx.2
  have hZO : (Z : Set X) ⊆ O := fun _ hx => hVO hx.1
  have hZm : ∀ x : (r.restrictSource Z hZr).source,
      (r.restrictSource Z hZr).map x ∈ O := by
    intro x
    exact hm ⟨x, x.property.1⟩
  let Y : TopologicalSpace.Opens X :=
    D ⊓ O ⊓ ⟨(E : Set X)ᶜ, E.finite_toSet.isClosed.isOpen_compl⟩
  have hr := f.isOpenHolomorphic_restrictSource hf T hTs
  have hpre : ∀ x : r.source, r.map x ∈ Y → (x : X) ∈ Z := by
    intro x hx
    refine ⟨hfull ⟨x, hTs x.property⟩ ?_ hx.1.2, x.property⟩
    intro hxF
    exact hx.2 (hFE ⟨x, hxF, f.totalize_eq (hTs x.property)⟩)
  have hh := r.regularValues_restrictAmbient_restrictSource hr O Z hZr hZO hZm Y
    (fun _ hx => hx.1.2) (fun _ hx => hreg ⟨hx.1.1, hx.2⟩) hpre
  refine ⟨fun _ hx => hx.1, ?_⟩
  intro y hy
  apply hh
  exact ⟨⟨hy.1, y.property⟩, fun he => hy.2
    ((mem_finiteStageOnAnchorComplement F E y).mpr he)⟩

end SurfaceDynamics.LocalMap

