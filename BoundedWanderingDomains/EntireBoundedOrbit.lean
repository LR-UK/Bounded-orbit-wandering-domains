/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import RiemannDynamics.BoundedWanderingSolution

open Set Metric Function Filter
open scoped Topology

-- Retain the instance expression used in the original statement.
section
attribute [local instance] instCommCStarAlgebraComplex

namespace BoundedWanderingDomains

/-- An entire transcendental function has no wandering Fatou component
containing a point with bounded orbit. -/
theorem no_bounded_wandering_domains_transcendental_entire
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hbounded : Bornology.IsBounded (Set.range (fun n : ℕ => (f^[n]) z))) :
    ¬ Pairwise (fun n m : ℕ => Disjoint (U n) (U m)) :=
  Unconditional.no_bounded_wandering_domains_transcendental_entire
    hf htrans hU hz hforward hbounded

end BoundedWanderingDomains

end
