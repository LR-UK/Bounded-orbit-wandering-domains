/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import RiemannDynamics.BoundedWanderingSolution

open Set Metric Function Filter
open scoped Topology

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

/-- A simply connected local trapped-component orbit cannot be wandering
if one point orbit stays in a compact subset of V. Eventual injectivity on
intrinsic discs and their compact confinement are proved, not assumed. -/
theorem no_local_bounded_wandering_domains
    {f : ℂ → ℂ} {V K : Set ℂ} {z : ℂ} {U : ℕ → Set ℂ}
    (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hf : AnalyticOnNhd ℂ f (closure V))
    (hn : ∀ x ∈ closure V, ¬EventuallyConst f (𝓝 x))
    (hK : IsCompact K) (hKV : K ⊆ V)
    (hz : z ∈ trappedInterior f V)
    (hU : ∀ n, U n = connectedComponentIn (trappedInterior f V) (f^[n] z))
    (hsc : ∀ n, IsSimplyConnected (U n))
    (hbounded : ∀ n, f^[n] z ∈ K) :
    ¬ Pairwise (fun n m : ℕ => Disjoint (U n) (U m)) :=
  Unconditional.no_local_bounded_wandering_domains
    hV hVc hf hn hK hKV hz hU hsc hbounded

#print axioms no_local_bounded_wandering_domains
#print axioms no_bounded_wandering_domains_transcendental_entire

end BoundedWanderingDomains
