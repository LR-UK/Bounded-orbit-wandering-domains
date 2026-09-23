import BoundedWanderingDomains.CoveringMetricInput
import BoundedWanderingDomains.EntireFatouBridge
import BoundedWanderingDomains.TrappedComponentCovering
import BoundedWanderingDomains.TrappedSimpleConnectivity
import BoundedWanderingDomains.BoundedPointWandering
import BoundedWanderingDomains.LocalBoundedPoint

/-! Both dynamical theorems with only disc-covering existence and its area
formula as classical input. The local theorem requires only one compactly contained point orbit. -/

open Set Metric Function Filter
open scoped Topology

namespace BoundedWanderingDomains

private theorem covering_metric_input_exists (h : ClassicalDiscCoveringsAndArea) :
    Nonempty AreaDeficit.FinitePunctureMetricInput := by
  obtain ⟨ρ, hp, hs, hc, hSchwarz, he, ha⟩ := classicalHyperbolicMetrics_of_coveringsAndArea h
  exact ⟨⟨ρ, hp, hs, hc, hSchwarz, he, ha⟩⟩

/-- An entire function cannot have a wandering Fatou component containing a
point with bounded orbit, conditional only on disc coverings and their area. -/
theorem no_bounded_wandering_domains_transcendental_entire_of_coveringsAndArea
    (hcover : ClassicalDiscCoveringsAndArea)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hbounded : Bornology.IsBounded (Set.range (fun n : ℕ => (f^[n]) z))) :
    ¬ Pairwise (fun n m : ℕ => Disjoint (U n) (U m)) := by
  obtain ⟨G⟩ := covering_metric_input_exists hcover
  obtain ⟨R, _, hR⟩ := hbounded.exists_pos_norm_le
  exact G.no_wandering_fatou_orbit_of_bounded_point hf
    (AreaDeficit.entire_nonpolynomial_no_constant_germ hf htrans) hU hz hforward
    ⟨R, fun n => hR _ ⟨n, rfl⟩⟩

/-- The local theorem from one compactly contained point orbit, with the
reduced classical input. Eventual intrinsic-disc injectivity is proved. -/
theorem no_local_bounded_wandering_domains_of_coveringsAndArea
    (hcover : ClassicalDiscCoveringsAndArea)
    {f : ℂ → ℂ} {V K : Set ℂ} {z : ℂ} {U : ℕ → Set ℂ}
    (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hf : AnalyticOnNhd ℂ f (closure V))
    (hn : ∀ x ∈ closure V, ¬EventuallyConst f (𝓝 x))
    (hK : IsCompact K) (hKV : K ⊆ V)
    (hz : z ∈ trappedInterior f V)
    (hU : ∀ n, U n = connectedComponentIn (trappedInterior f V) (f^[n] z))
    (hsc : ∀ n, IsSimplyConnected (U n))
    (hbounded : ∀ n, f^[n] z ∈ K) :
    ¬ Pairwise (fun n m : ℕ => Disjoint (U n) (U m)) := by
  obtain ⟨G⟩ := covering_metric_input_exists hcover
  intro hdisj
  have hi := AreaDeficit.trapped_interior_forward (AreaDeficit.analytic_locally_open
    (hf.mono subset_closure) (fun x hx => hn x (subset_closure hx)))
  exact G.no_wandering_local_orbit_of_compact_point hV hVc hf hn hK hKV
    (fun n => hi.iterate n hz) hU (fun n => by simp [iterate_succ_apply'])
    hsc hbounded hdisj

end BoundedWanderingDomains
