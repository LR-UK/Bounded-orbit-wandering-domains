import BoundedWanderingDomains.SubmissionDefinitions
import BoundedWanderingDomains.EntireFatouBridge
import BoundedWanderingDomains.TrappedComponentCovering
import BoundedWanderingDomains.TrappedSimpleConnectivity
import BoundedWanderingDomains.BoundedPointWandering

open Set Metric Function Filter MeasureTheory
open scoped Topology ENNReal

namespace BoundedWanderingDomains

private theorem metric_input_exists (h : ClassicalHyperbolicMetrics) :
    Nonempty AreaDeficit.FinitePunctureMetricInput := by
  obtain ⟨ρ, hp, hs, hc, hSchwarz, he, ha⟩ := h
  exact ⟨⟨ρ, hp, hs, hc, hSchwarz, he, ha⟩⟩

/-- Local absence of compactly contained wandering components, conditional
on the classical metric facts and eventual intrinsic-disc injectivity. -/
theorem no_local_bounded_wandering_domains
    (hmetric : ClassicalHyperbolicMetrics)
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
    ¬ Pairwise (fun n m : ℕ => Disjoint (U n) (U m)) := by
  obtain ⟨G⟩ := metric_input_exists hmetric
  intro hdisj
  have hi := AreaDeficit.trapped_interior_forward (AreaDeficit.analytic_locally_open
    (hf.mono subset_closure) (fun x hx => hn x (subset_closure hx)))
  exact G.no_wandering_component_orbit hV hVc hf hn hK hKV
    (fun n => hi.iterate n hz) hU (fun n => by simp [iterate_succ_apply'])
    hdisj hbounded hsc hinj

/-- Entire-function version with boundedness of the forward orbit of one
point in the Fatou component. The auxiliary simple connectivity and local
inverse-branch assertions are derived, not assumed. -/
theorem no_bounded_wandering_domains_transcendental_entire
    (hmetric : ClassicalHyperbolicMetrics)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hbounded : Bornology.IsBounded (Set.range (fun n : ℕ => (f^[n]) z))) :
    ¬ Pairwise (fun n m : ℕ => Disjoint (U n) (U m)) := by
  obtain ⟨G⟩ := metric_input_exists hmetric
  obtain ⟨R, _, hR⟩ := hbounded.exists_pos_norm_le
  exact G.no_wandering_fatou_orbit_of_bounded_point hf
    (AreaDeficit.entire_nonpolynomial_no_constant_germ hf htrans) hU hz hforward
    ⟨R, fun n => hR _ ⟨n, rfl⟩⟩

end BoundedWanderingDomains

#print axioms BoundedWanderingDomains.no_local_bounded_wandering_domains
#print axioms BoundedWanderingDomains.no_bounded_wandering_domains_transcendental_entire
