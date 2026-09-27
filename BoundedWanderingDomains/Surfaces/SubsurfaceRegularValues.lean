/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.LocalMapSubsurface
import BoundedWanderingDomains.Surfaces.SurfaceSingularCovering

open Set Function Topology
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X]

/-- Restricting source and ambient surface preserves a regular-value
neighbourhood when no preimage over that neighbourhood has been removed. -/
theorem regularValues_restrictAmbient_restrictSource
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (O V : TopologicalSpace.Opens X) (hVs : (V : Set X) ⊆ f.source)
    (hVO : (V : Set X) ⊆ O)
    (hm : ∀ x : (f.restrictSource V hVs).source, (f.restrictSource V hVs).map x ∈ O)
    (Y : TopologicalSpace.Opens X) (hYO : (Y : Set X) ⊆ O)
    (hYreg : (Y : Set X) ⊆ f.regularValues)
    (hpre : ∀ x : f.source, f.map x ∈ Y → (x : X) ∈ V) :
    Subtype.val ⁻¹' (Y : Set X) ⊆
      ((f.restrictSource V hVs).restrictAmbient O hVO hm).regularValues := by
  let r := f.restrictSource V hVs
  let g := r.restrictAmbient O hVO hm
  let T : Set O := Subtype.val ⁻¹' (Y : Set X)
  have hT : IsOpen T := Y.isOpen.preimage continuous_subtype_val
  let eT : T ≃ₜ Y :=
    { toFun := fun x => ⟨((x : O) : X), x.property⟩
      invFun := fun y => ⟨⟨(y : X), hYO y.property⟩, y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let eS : (g.map ⁻¹' T) ≃ₜ (f.map ⁻¹' (Y : Set X)) :=
    { toFun := fun x => ⟨⟨(((x : g.source) : O) : X), hVs (x : g.source).property⟩, x.property⟩
      invFun := fun x => ⟨⟨⟨((x : f.source) : X), hVO (hpre x x.property)⟩,
        hpre x x.property⟩, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hbase : IsCoveringMap ((Y : Set X).restrictPreimage f.map) :=
    (f.isCoveringMapOn_compl_singularValues.mono (by simpa only [singularValues, compl_compl] using hYreg)).isCoveringMap_restrictPreimage
  have htransport := (hbase.comp_homeomorph eS).homeomorph_comp eT.symm
  have heq : eT.symm ∘ (Y : Set X).restrictPreimage f.map ∘ eS = T.restrictPreimage g.map := by
    funext x
    rfl
  rw [heq] at htransport
  have hg : IsOpenHolomorphic g := r.isOpenHolomorphic_restrictAmbient
    (f.isOpenHolomorphic_restrictSource hf V hVs) O hVO hm
  have hcov : IsCoveringMapOn g.map T :=
    IsCoveringMapOn.of_isCoveringMap_restrictPreimage T hT (hT.preimage hg.2.continuous) htransport
  have hrange : T ⊆ range g.map := by
    intro y hy
    obtain ⟨A, hAo, hyA, hArange, hAcov⟩ := hYreg hy
    obtain ⟨x, hx⟩ := hArange hyA
    have hxY : f.map x ∈ Y := hx.symm ▸ hy
    refine ⟨⟨⟨x, hVO (hpre x hxY)⟩, hpre x hxY⟩, ?_⟩
    exact Subtype.ext hx
  intro y hy
  exact ⟨T, hT, hy, hrange, hcov⟩

theorem singularValues_restrictAmbient_restrictSource_subset
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (O V : TopologicalSpace.Opens X) (hVs : (V : Set X) ⊆ f.source)
    (hVO : (V : Set X) ⊆ O)
    (hm : ∀ x : (f.restrictSource V hVs).source, (f.restrictSource V hVs).map x ∈ O)
    (hfull : ∀ x : f.source, (x : X) ∈ O → f.map x ∈ O → (x : X) ∈ V)
    {B : Set X} (hB : IsClosed B)
    (hremoved : ∀ x : f.source, (x : X) ∉ O → f.map x ∈ B) :
    Subtype.val '' ((f.restrictSource V hVs).restrictAmbient O hVO hm).singularValues ⊆
      f.singularValues ∪ B := by
  classical
  rintro y ⟨yo, hyo, rfl⟩
  by_contra hh
  have hyr : (yo : X) ∈ f.regularValues := by
    by_contra hr
    exact hh (Or.inl hr)
  have hyB : (yo : X) ∉ B := fun hb => hh (Or.inr hb)
  let Y : TopologicalSpace.Opens X :=
    O ⊓ ⟨f.regularValues, f.isOpen_regularValues⟩ ⊓ ⟨Bᶜ, hB.isOpen_compl⟩
  apply hyo
  apply f.regularValues_restrictAmbient_restrictSource hf O V hVs hVO hm Y
    (fun _ hx => hx.1.1) (fun _ hx => hx.1.2)
  · intro x hx
    apply hfull x _ hx.1.1
    by_contra ho
    exact hx.2 (hremoved x ho)
  · exact ⟨⟨yo.property, hyr⟩, hyB⟩

end SurfaceDynamics.LocalMap

#print axioms SurfaceDynamics.LocalMap.regularValues_restrictAmbient_restrictSource
