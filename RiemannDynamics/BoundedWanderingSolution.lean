/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import RiemannDynamics.Uniformization.PuncturedPlaneCovering
import BoundedWanderingDomains.CoveringTotalArea
import CoveringSolution

/-!
# Bounded-orbit wandering domains: complete formalisation

The disc covering is supplied by the formalised uniformisation theorem.
The area formula is proved by logarithmic cutoffs, Green's identity and Fatou's lemma.
Neither covering existence nor the area formula is assumed by the results below.
-/

open Set Metric Function Filter
open scoped Topology

namespace BoundedWanderingDomains.Unconditional

theorem classicalDiscCoveringsAndArea : ClassicalDiscCoveringsAndArea := by
  intro P hP
  obtain ⟨p, hp⟩ := RiemannDynamics.exists_disc_covering_finitely_punctured_plane P hP
  exact ⟨p, hp, hp.total_area hP⟩

theorem classicalHyperbolicMetrics : ClassicalHyperbolicMetrics :=
  classicalHyperbolicMetrics_of_coveringsAndArea classicalDiscCoveringsAndArea

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
  no_bounded_wandering_domains_transcendental_entire_of_coveringsAndArea
    classicalDiscCoveringsAndArea hf htrans hU hz hforward hbounded

/-- The local theorem, with precisely the dynamical hypotheses of the frozen
submission and with the classical metric package now proved. -/
theorem no_local_bounded_wandering_domains
    {f : ℂ → ℂ} {V K : Set ℂ} {z : ℂ} {U : ℕ → Set ℂ}
    (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hf : AnalyticOnNhd ℂ f (closure V))
    (hn : ∀ x ∈ closure V, ¬EventuallyConst f (𝓝 x))
    (hK : IsCompact K) (hKV : K ⊆ V)
    (hz : z ∈ trappedInterior f V)
    (hU : ∀ n, U n = connectedComponentIn (trappedInterior f V) (f^[n] z))
    (hsc : ∀ n, IsSimplyConnected (U n))
    (hbounded : ∀ n, U n ⊆ K)
    (hinj : EventuallyInjectiveOnLargeDiscs f U (fun n => f^[n] z)) :
    ¬ Pairwise (fun n m : ℕ => Disjoint (U n) (U m)) :=
  no_local_bounded_wandering_domains_of_coveringsAndArea classicalDiscCoveringsAndArea
    hV hVc hf hn hK hKV hz hU hsc hbounded hinj

#print axioms classicalDiscCoveringsAndArea
#print axioms classicalHyperbolicMetrics
#print axioms no_bounded_wandering_domains_transcendental_entire
#print axioms no_local_bounded_wandering_domains

end BoundedWanderingDomains.Unconditional
