module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.CoordinateDiscParam

@[expose] public section

/-! # Embedded analytic target discs and change of ambient surface -/

open Set Topology
open AreaDeficit.Surfaces
open scoped Manifold

namespace SurfaceDynamics

structure EmbeddedDisc (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] where
  param : unitDisc → X
  holomorphic : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) param
  embedding : IsOpenEmbedding param

namespace EmbeddedDisc

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

def carrier (Q : EmbeddedDisc X) : TopologicalSpace.Opens X :=
  ⟨range Q.param, Q.embedding.isOpen_range⟩

noncomputable def center (Q : EmbeddedDisc X) : X := Q.param discZero

theorem center_mem (Q : EmbeddedDisc X) : Q.center ∈ Q.carrier := mem_range_self _

theorem isConnected_carrier (Q : EmbeddedDisc X) : IsConnected (Q.carrier : Set X) := by
  let discSimplyConnected : SimplyConnectedSpace unitDisc := unitDisc_simplyConnected
  exact isConnected_range Q.embedding.continuous

noncomputable def ofCoordDisk [IsManifold 𝓘(ℂ) 1 X] (Q : RiemannDynamics.CoordDisk X) :
    EmbeddedDisc X := ⟨Q.param, Q.mdifferentiable_param, Q.isOpenEmbedding_param⟩

def inAmbient (O : TopologicalSpace.Opens X) (Q : EmbeddedDisc O) : EmbeddedDisc X where
  param := fun w => (Q.param w : X)
  holomorphic := (mdifferentiable_subtype_val O).comp Q.holomorphic
  embedding := O.isOpen.isOpenEmbedding_subtypeVal.comp Q.embedding

end EmbeddedDisc
end SurfaceDynamics
