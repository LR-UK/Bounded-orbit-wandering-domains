module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import Mathlib.Geometry.Manifold.Complex
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

@[expose] public section

/-! # Riemann surfaces with a supplied holomorphic disc covering

Research interface, independent of a general uniformisation theorem. The target
uses Mathlib's complex-manifold structure. Surjectivity is explicit because
Mathlib's covering maps are allowed to have empty fibres.
-/

open Set Metric Function
open scoped Manifold Topology

namespace AreaDeficit.Surfaces

def unitDisc : TopologicalSpace.Opens ℂ := ⟨ball 0 1, isOpen_ball⟩

/-- A holomorphic universal covering supplied as data, rather than obtained
from an assumed uniformisation theorem. -/
structure DiscCover (M : Type*) [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) 1 M] where
  projection : unitDisc → M
  holomorphic : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) projection
  covering : IsCoveringMap projection
  surjective : Surjective projection

theorem unitDisc_simplyConnected : SimplyConnectedSpace unitDisc := by
  let : ContractibleSpace (ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).contractibleSpace (nonempty_ball.mpr (by norm_num))
  change SimplyConnectedSpace (ball (0 : ℂ) 1)
  infer_instance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

theorem DiscCover.continuous (p : DiscCover M) : Continuous p.projection :=
  p.covering.continuous

theorem DiscCover.isOpenMap (p : DiscCover M) : IsOpenMap p.projection :=
  p.covering.isOpenMap

end AreaDeficit.Surfaces
