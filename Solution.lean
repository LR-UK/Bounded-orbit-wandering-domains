import SubmissionDefinitions
import EntireFatouBridge

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

/-- Entire-function version for an actual Fatou-component orbit.
"Bounded" means a single bound on the union of all components.
Simple connectivity and eventual intrinsic-disc injectivity are explicit. -/
theorem no_bounded_wandering_domains_transcendental_entire
    (hmetric : ClassicalHyperbolicMetrics)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hsc : ∀ n, IsSimplyConnected (U n))
    (hbounded : Bornology.IsBounded (⋃ n, U n))
    (hinj : EventuallyInjectiveOnLargeDiscs f U (fun n => f^[n] z)) :
    ¬ Pairwise (fun n m : ℕ => Disjoint (U n) (U m)) := by
  obtain ⟨R, hR, hbound⟩ := hbounded.exists_pos_norm_le
  let K : Set ℂ := closedBall 0 R
  let V : Set ℂ := ball 0 (R + 1)
  have hUK : ∀ n, U n ⊆ K := by
    intro n w hw
    exact mem_closedBall_zero_iff.mpr (hbound w (mem_iUnion.mpr ⟨n, hw⟩))
  have hKV : K ⊆ V := closedBall_subset_ball (by linarith)
  have hn := AreaDeficit.entire_nonpolynomial_no_constant_germ hf htrans
  obtain ⟨hzT, hUT⟩ := AreaDeficit.fatou_orbit_eq_trapped_components hf hn
    isBounded_ball hU hforward (fun n => (hUK n).trans hKV) hz
  have hVc : IsCompact (closure V) := by
    dsimp [V]
    rw [closure_ball (0 : ℂ) (by linarith : R + 1 ≠ 0)]
    exact isCompact_closedBall _ _
  exact no_local_bounded_wandering_domains hmetric isOpen_ball hVc
    ((hf.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _))
    (fun x _ => hn x) (isCompact_closedBall _ _) hKV
    (by simpa only [Function.iterate_zero_apply, trappedInterior,
      AreaDeficit.trappedSet] using hzT 0) hUT hsc hUK hinj

end BoundedWanderingDomains

#print axioms BoundedWanderingDomains.no_local_bounded_wandering_domains
#print axioms BoundedWanderingDomains.no_bounded_wandering_domains_transcendental_entire
