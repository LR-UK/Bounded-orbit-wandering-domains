module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.ControlledComponents
public import BoundedWanderingDomains.Surfaces.SaturationDynamics

@[expose] public section

/-! # Measurable orbit sets for finite component-control configurations -/

open Set Function MeasureTheory Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

def componentControlRegion
    (f : LocalMap X) (hf : Continuous f.map) {ι : Type*}
    (D : ι → TopologicalSpace.Opens X) (L : ι → ℕ → Set X)
    (I : Finset (ι × ℕ)) (E : Set X) : Set X :=
  ⋃ i : I, (f.finiteObstructionSource hf (D i.val.1) E : Set X) ∩
    f.totalize ⁻¹' L i.val.1 i.val.2

def componentControlTail
    (f : LocalMap X) (hf : Continuous f.map) {ι : Type*}
    (D : ι → TopologicalSpace.Opens X) (L : ι → ℕ → Set X)
    (I : Finset (ι × ℕ)) (E K A : Set X) (N : ℕ) : Set X :=
  A ∩ ⋂ n : ℕ, (f.totalize^[n + N]) ⁻¹' (K ∩ f.componentControlRegion hf D L I E)

variable [MeasurableSpace X] [BorelSpace X]

theorem measurableSet_componentControlRegion
    (f : LocalMap X) (hf : Continuous f.map) {ι : Type*}
    (D : ι → TopologicalSpace.Opens X) (L : ι → ℕ → Set X)
    (hL : ∀ i n, MeasurableSet (L i n)) (I : Finset (ι × ℕ)) (E : Set X) :
    MeasurableSet (f.componentControlRegion hf D L I E) := by
  exact MeasurableSet.iUnion (fun i : I =>
    (f.finiteObstructionSource hf (D i.val.1) E).isOpen.measurableSet.inter
      ((hL i.val.1 i.val.2).preimage (f.measurable_totalize hf)))

theorem measurableSet_componentControlTail
    (f : LocalMap X) (hf : Continuous f.map) {ι : Type*}
    (D : ι → TopologicalSpace.Opens X) (L : ι → ℕ → Set X)
    (hL : ∀ i n, MeasurableSet (L i n)) (I : Finset (ι × ℕ))
    (E K A : Set X) (hK : MeasurableSet K) (hA : MeasurableSet A) (N : ℕ) :
    MeasurableSet (f.componentControlTail hf D L I E K A N) := by
  exact hA.inter (MeasurableSet.iInter (fun n =>
    (hK.inter (f.measurableSet_componentControlRegion hf D L hL I E)).preimage
      ((f.measurable_totalize hf).iterate (n + N))))

end SurfaceDynamics.LocalMap
