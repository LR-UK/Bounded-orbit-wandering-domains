module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.CountableComponents

@[expose] public section

/-! # A countable pool for finite component obstruction sets -/

open Set Function Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem componentSingularValues_eq_of_inverseComponentSource_eq
    (f : LocalMap X) (hf : Continuous f.map) (D : TopologicalSpace.Opens X)
    (a b : f.source)
    (h : (f.inverseComponentSource hf D a : Set X) = f.inverseComponentSource hf D b) :
    f.componentSingularValues hf D a = f.componentSingularValues hf D b := by
  have he : f.inverseComponentSource hf D a = f.inverseComponentSource hf D b :=
    TopologicalSpace.Opens.ext h
  have hm : f.inverseComponentMap hf D a = f.inverseComponentMap hf D b := by
    simp only [inverseComponentMap, he]
  exact congrArg (fun g : LocalMap X =>
    g.singularValues ∩ closure (range g.map) ∩ (D : Set X)) hm

variable [SecondCountableTopology X]

theorem exists_countable_pool_of_finite_component_obstructions
    (f : LocalMap X) (hf : Continuous f.map) (D : TopologicalSpace.Opens X) :
    ∃ T : Set X, T.Countable ∧ ∀ a : f.source,
      (f.componentSingularValues hf D a).Finite → f.componentSingularValues hf D a ⊆ T := by
  classical
  let C : Set (Set X) := range (fun a : f.source => (f.inverseComponentSource hf D a : Set X))
  let countableComponents : Countable C := (f.countable_inverseComponentSources hf D).to_subtype
  have hrep : ∀ V : C, ∃ a : f.source, (f.inverseComponentSource hf D a : Set X) = V :=
    fun V => V.2
  choose a ha using hrep
  let S : C → Set X := fun V => if (f.componentSingularValues hf D (a V)).Finite
    then f.componentSingularValues hf D (a V) else ∅
  have hS : ∀ V, (S V).Countable := by
    intro V
    dsimp [S]
    split_ifs with h
    · exact h.countable
    · exact countable_empty
  refine ⟨⋃ V, S V, countable_iUnion hS, ?_⟩
  intro b hb
  let V : C := ⟨f.inverseComponentSource hf D b, mem_range_self b⟩
  have he := f.componentSingularValues_eq_of_inverseComponentSource_eq hf D (a V) b (ha V)
  have hfin : (f.componentSingularValues hf D (a V)).Finite := he.symm ▸ hb
  intro y hy
  apply mem_iUnion.mpr
  refine ⟨V, ?_⟩
  simp only [S, ite_eq_left hfin, he]
  exact hy

/-- For a countable family of target discs, all finite sets of genuine
component obstructions draw their values from a single countable pool. -/
theorem exists_countable_pool_of_finite_obstructions
    (f : LocalMap X) (hf : Continuous f.map) {ι : Type*} [Countable ι]
    (D : ι → TopologicalSpace.Opens X) :
    ∃ T : Set X, T.Countable ∧ ∀ i (a : f.source),
      (f.componentSingularValues hf (D i) a).Finite →
        f.componentSingularValues hf (D i) a ⊆ T := by
  choose T hT hsub using fun i => f.exists_countable_pool_of_finite_component_obstructions hf (D i)
  refine ⟨⋃ i, T i, countable_iUnion hT, ?_⟩
  intro i a ha
  exact (hsub i a ha).trans (subset_iUnion T i)

end SurfaceDynamics.LocalMap
