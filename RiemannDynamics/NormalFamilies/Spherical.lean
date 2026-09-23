/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.NormalFamilies.Basic
import RiemannDynamics.Sphere.SphericalMetric

/-!
# Spherical-metric setup for meromorphic normal families

This file installs `MetricSpace` (and hence `UniformSpace`) instances on the
Riemann sphere `ℂ̂ = OnePoint ℂ` derived from the spherical (chordal) metric
defined in `Sphere/SphericalMetric.lean`. The induced topology coincides with
the one already on `OnePoint ℂ` by `sphericalDist_induces_topology`.

With these instances in place, `IsNormal 𝓕 U` from `NormalFamilies/Basic.lean`
specializes to the meromorphic case (`Y = ℂ̂`) — sequences in a family of
meromorphic functions `ℂ → ℂ̂` having locally-uniformly-convergent
subsequences with respect to the spherical metric.
-/

namespace RiemannDynamics

open OnePoint

/-- The spherical metric makes `ℂ̂` a metric space. The induced topology agrees
with the existing one-point-compactification topology, via
`sphericalDist_induces_topology`. -/
noncomputable instance : MetricSpace (OnePoint ℂ) :=
  let m : MetricSpace (OnePoint ℂ) :=
    { dist := sphericalDist
      dist_self := fun z => (sphericalDist_eq_zero_iff z z).mpr rfl
      dist_comm := sphericalDist_comm
      dist_triangle := sphericalDist_triangle
      eq_of_dist_eq_zero := fun {z w} h => (sphericalDist_eq_zero_iff z w).mp h }
  m.replaceTopology <| by
    apply TopologicalSpace.ext
    ext s
    rw [sphericalDist_induces_topology, @Metric.isOpen_iff _ m.toPseudoMetricSpace]
    refine forall_congr' fun z => forall_congr' fun _ => ?_
    refine exists_congr fun ε => and_congr Iff.rfl ?_
    constructor
    · intro h y hy
      exact h y (by
        change @dist (OnePoint ℂ) m.toPseudoMetricSpace.toDist y z < ε at hy
        show sphericalDist z y < ε
        rw [sphericalDist_comm]; exact hy)
    · intro h y hy
      apply h
      change @dist (OnePoint ℂ) m.toPseudoMetricSpace.toDist y z < ε
      rw [show (@dist (OnePoint ℂ) m.toPseudoMetricSpace.toDist y z) = sphericalDist y z from rfl,
          sphericalDist_comm]
      exact hy

end RiemannDynamics
