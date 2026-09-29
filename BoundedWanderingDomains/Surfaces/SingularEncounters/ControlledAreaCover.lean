module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.ControlledComponents
public import BoundedWanderingDomains.Surfaces.SingularEncounters.FiniteObstructions

@[expose] public section

/-! # Countable regular covers supplied by finite component control -/

open Set Function Topology
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]

theorem countable_regular_cover_of_component_control
    (f : LocalMap X) (hf : IsOpenHolomorphic f) {ι : Type*} [Fintype ι]
    (D : ι → TopologicalSpace.Opens X) (hD : ∀ i, IsConnected (D i : Set X))
    (L : ι → Set X) (E : Finset X)
    {W : Set X} (hW : W.Nonempty) (hWs : W ⊆ f.source)
    (havoid : ∀ x ∈ W, f.totalize x ∉ E)
    (hcontrol : ∀ x ∈ W, ∃ i, f.totalize x ∈ L i ∧
      x ∈ f.finiteObstructionSource hf.2.continuous (D i) (E : Set X)) :
    ∃ (V : ℕ → TopologicalSpace.Opens X) (hV : ∀ n, (V n : Set X) ⊆ f.source)
      (label : ℕ → ι),
      (∀ n, (D (label n) : Set X) \ (E : Set X) ⊆
        (f.restrictSource (V n) (hV n)).regularValues) ∧
      W ⊆ ⋃ n, (V n : Set X) ∩ f.totalize ⁻¹' L (label n) := by
  classical
  let bases : ι → Set f.source := fun i =>
    {a | f.map a ∈ D i ∧ f.map a ∉ E ∧ f.componentSingularValues hf.2.continuous (D i) a ⊆ E}
  let cover (i : ι) (a : bases i) : TopologicalSpace.Opens X :=
    f.inverseComponentSource hf.2.continuous (D i) a
  choose T hT hTeq using fun i => TopologicalSpace.isOpen_iUnion_countable
    (fun a : bases i => (cover i a : Set X)) (fun a => (cover i a).isOpen)
  let componentCountable (i : ι) : Countable (T i) := (hT i).to_subtype
  let J := Σ i, T i
  let V : J → TopologicalSpace.Opens X := fun j => cover j.1 j.2.1
  have hcover : W ⊆ ⋃ j : J, (V j : Set X) ∩ f.totalize ⁻¹' L j.1 := by
    intro x hx
    obtain ⟨i, hxi, hxgood⟩ := hcontrol x hx
    let a : f.source := ⟨x, hWs hx⟩
    have hdata := (f.mem_finiteObstructionSource_iff hf.2.continuous (D i) (E : Set X) a).mp hxgood
    have haE : f.map a ∉ E := by
      simpa only [a, ← f.totalize_eq (hWs hx)] using havoid x hx
    let b : bases i := ⟨a, hdata.1, haE, hdata.2⟩
    have hxunion : x ∈ ⋃ b : bases i, (cover i b : Set X) :=
      mem_iUnion.mpr ⟨b, a, mem_connectedComponentIn hdata.1, rfl⟩
    rw [← hTeq i] at hxunion
    obtain ⟨b', hb', hxb'⟩ := mem_iUnion₂.mp hxunion
    exact mem_iUnion.mpr ⟨⟨i, ⟨b', hb'⟩⟩, hxb', hxi⟩
  have hJ : Nonempty J := by
    obtain ⟨x, hx⟩ := hW
    obtain ⟨j, _⟩ := mem_iUnion.mp (hcover hx)
    exact ⟨j⟩
  obtain ⟨q, hq⟩ := countable_iff_exists_surjective.mp (inferInstance : Countable J)
  refine ⟨V ∘ q, fun n => f.inverseComponentSource_subset hf.2.continuous (D (q n).1) (q n).2.1.1,
    fun n => (q n).1, ?_, ?_⟩
  · intro n
    let a := (q n).2.1
    exact f.inverseComponent_regularValues_of_finite_obstructions hf (D (q n).1) (hD _)
      E.finite_toSet a.1 a.2.1 a.2.2.1 a.2.2.2
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hx)
    obtain ⟨n, rfl⟩ := hq j
    exact mem_iUnion.mpr ⟨n, hj⟩

end SurfaceDynamics.LocalMap
