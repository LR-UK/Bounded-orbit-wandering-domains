module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.EntireBoundedOrbit
public import BoundedWanderingDomains.GlobalLimitStatements
public import BoundedWanderingDomains.LocalUniformSingularLimits

@[expose] public section

open Set Metric Function Filter
open scoped Topology

namespace BoundedWanderingDomains

/-- A local trapped-component orbit cannot be wandering
if one point orbit stays in a compact subset of V. Eventual injectivity on
intrinsic discs, their eventual embedding and compact confinement are proved. -/
theorem no_local_bounded_wandering_domains
    {f : ℂ → ℂ} {V K : Set ℂ} {z : ℂ} {U : ℕ → Set ℂ}
    (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hf : AnalyticOnNhd ℂ f (closure V))
    (hn : ∀ x ∈ closure V, ¬EventuallyConst f (𝓝 x))
    (hK : IsCompact K) (hKV : K ⊆ V)
    (hz : z ∈ trappedInterior f V)
    (hU : ∀ n, U n = connectedComponentIn (trappedInterior f V) (f^[n] z))
    (hbounded : ∀ n, f^[n] z ∈ K) :
    ¬ Pairwise (fun n m : ℕ => Disjoint (U n) (U m)) :=
  Unconditional.no_local_bounded_wandering_domains
    hV hVc hf hn hK hKV hz hU hbounded

end BoundedWanderingDomains
