import EremenkosConjecture.RayGeometry
import EremenkosConjecture.ComponentBarriers
import EremenkosConjecture.ScaffoldingOrbits
import ComplexDynamics.BoundedNormality
import ComplexDynamics.Transcendence

/-! # Dynamical conclusion of the Section 7 construction

This module proves the implication from the specified analytic construction
data to the counterexample conclusions. Existence of the construction data
is a separate obligation; the structure below is not an existence theorem.
-/

open Set Metric Function Filter ComplexDynamics
open scoped Topology

namespace EremenkosConjecture

open Scaffolding

/-- Orbit and barrier data sufficient for the conclusion of Theorem 7.1,
with its endpoint translated to `ζ`. The approximation construction must
supply all these fields. -/
structure RayConstructionData (f : ℂ → ℂ) (ζ : ℂ) : Prop where
  entire : IsEntire f
  widths : ∃ a b : ℕ → ℝ, (∀ j, 0 < a j) ∧ (∀ j, 0 < b j) ∧
    Tendsto a atTop (𝓝 0) ∧ Tendsto b atTop (𝓝 0) ∧
    ∀ j, MapsTo (f^[returnTime j + 1]) (frontier (closedHalfStrip ζ (a j) (b j))) trappingDisk
  trapping : MapsTo f trappingDisk (ball 0 (1 / 2))
  excursions : ∀ j, MapsTo (f^[returnTime j]) (horizontalRay ζ) (targetStrip j)
  returns : ∀ j, MapsTo (f^[returnTime j + 1]) (horizontalRay ζ) (sourceStrip 0)
  boundedReturns : ∀ z ∈ horizontalRay ζ, z ≠ ζ →
    ∀ᶠ j in atTop, |((f^[returnTime j + 1]) z).re| ≤ 1
  endpoint : ∀ j n, returnTime j + 1 ≤ n → n ≤ returnTime (j + 1) →
    (j : ℝ) ≤ |((f^[n]) ζ).re|

theorem RayConstructionData.endpoint_escapes {f : ℂ → ℂ} {ζ : ℂ}
    (D : RayConstructionData f ζ) : ζ ∈ escapingSet f :=
  mem_escapingSet_of_return_blocks D.endpoint

theorem RayConstructionData.ray_bungee {f : ℂ → ℂ} {ζ : ℂ}
    (D : RayConstructionData f ζ) {z : ℂ} (hz : z ∈ horizontalRay ζ) (hne : z ≠ ζ) :
    z ∈ bungeeSet f :=
  mem_bungeeSet_of_strip_returns (fun j => D.excursions j hz)
    (fun j => D.returns j hz) (D.boundedReturns z hz hne)

theorem RayConstructionData.conclusions {f : ℂ → ℂ} {ζ : ℂ}
    (D : RayConstructionData f ζ) :
    IsTranscendentalEntire f ∧ horizontalRay ζ ⊆ juliaSet f ∧ ζ ∈ escapingSet f ∧
    horizontalRay ζ \ {ζ} ⊆ bungeeSet f ∧
    connectedComponentIn (juliaSet f ∪ escapingSet f ∪ bungeeSet f) ζ = horizontalRay ζ ∧
    connectedComponentIn (escapingSet f) ζ = {ζ} := by
  obtain ⟨a, b, ha, hb, ha0, hb0, hboundary⟩ := D.widths
  let K : ℕ → Set ℂ := fun j => closedHalfStrip ζ (a j) (b j)
  have hK : ∀ j, IsClosed (K j) := fun j => isClosed_closedHalfStrip ζ (a j) (b j)
  have hinside : ∀ j, horizontalRay ζ ⊆ interior (K j) := fun j =>
    horizontalRay_subset_interior_halfStrip (ha j) (hb j)
  have hinter : (⋂ j, K j) = horizontalRay ζ :=
    iInter_closedHalfStrip_eq_ray (fun j => (ha j).le) (fun j => (hb j).le) ha0 hb0
  have htrap : MapsTo f trappingDisk trappingDisk :=
    D.trapping.mono_right ball_subset_closedBall
  have htrapped : ∀ j, frontier (K j) ⊆ trappedSet f trappingDisk :=
    fun j _ hz => mem_trappedSet_of_iterate_mem htrap (hboundary j hz)
  have hbounded : ∀ j, frontier (K j) ⊆ boundedOrbitSet f := fun j =>
    (htrapped j).trans (trappedSet_subset_boundedOrbitSet isBounded_closedBall)
  have hfatou : ∀ j, frontier (K j) ⊆ fatouSet f := by
    intro j z hz
    have hentry : (f^[returnTime j + 1 + 1]) z ∈ ball 0 (1 / 2) := by
      rw [iterate_succ_apply']
      exact D.trapping (hboundary j hz)
    exact mem_fatouSet_of_iterate_mem_bounded_invariant D.entire isOpen_ball isBounded_ball
      (D.trapping.mono_left ball_subset_closedBall) hentry
  have hclosure : horizontalRay ζ ⊆ closure (trappedSet f trappingDisk) := by
    have H := frontier_subset_closure_union_frontiers (isClosed_horizontalRay ζ) K hK
      (fun j => (hinside j).trans interior_subset) hinter
    rw [frontier_horizontalRay] at H
    exact H.trans (closure_mono (iUnion_subset htrapped))
  have hjulia : horizontalRay ζ ⊆ juliaSet f := by
    intro z hz
    exact mem_juliaSet_of_escape_subsequence_of_closure_trappedSet D.entire.continuous
      (isCompact_closedBall 0 (1 / 2)) strictMono_returnTime
      (tendsto_norm_of_targetStrip_excursions (fun j => D.excursions j hz)) (hclosure hz)
  have hζ : ζ ∈ horizontalRay ζ := mem_horizontalRay ζ
  have hbungee : horizontalRay ζ \ {ζ} ⊆ bungeeSet f := fun z hz =>
    D.ray_bungee hz.1 (by simpa only [mem_singleton_iff] using hz.2)
  have hdisj : ∀ j, Disjoint (juliaSet f ∪ escapingSet f ∪ bungeeSet f) (frontier (K j)) := by
    intro j
    apply Set.disjoint_left.mpr
    intro z hz hzK
    rcases hz with (hJ | hI) | hBU
    · exact hJ (hfatou j hzK)
    · exact Set.disjoint_left.mp (disjoint_boundedOrbitSet_escapingSet f) (hbounded j hzK) hI
    · exact (mem_bungeeSet_iff.mp hBU).1 (hbounded j hzK)
  have hcomponent := connectedComponentIn_eq_of_closed_barriers
    (isConnected_horizontalRay ζ).isPreconnected
    (show horizontalRay ζ ⊆ juliaSet f ∪ escapingSet f ∪ bungeeSet f from
      fun z hz => Or.inl (Or.inl (hjulia hz))) hK hinside hinter hdisj hζ
  have hsingle : connectedComponentIn (escapingSet f) ζ = {ζ} := by
    apply connectedComponentIn_eq_singleton_of_closed_barriers D.endpoint_escapes hζ
      hK hinside hinter (fun j => (hdisj j).mono_left (fun _ h => Or.inl (Or.inr h)))
    intro z hz
    by_contra hn
    exact (mem_bungeeSet_iff.mp (hbungee ⟨hz.2, hn⟩)).2 hz.1
  obtain ⟨u, hu, huinfty⟩ := exists_unbounded_frontier_sequence (ha 0).le (hb 0).le
  have htrans : IsTranscendentalEntire f :=
    isTranscendentalEntire_of_escape_and_bounded_values D.entire D.endpoint_escapes u huinfty
      (1 / 2) (fun n => by
        have H := hboundary 0 (hu n)
        simpa only [returnTime_zero, zero_add, iterate_one, trappingDisk,
          mem_closedBall, dist_zero_right] using H)
  exact ⟨htrans, hjulia, D.endpoint_escapes, hbungee, hcomponent, hsingle⟩

end EremenkosConjecture
