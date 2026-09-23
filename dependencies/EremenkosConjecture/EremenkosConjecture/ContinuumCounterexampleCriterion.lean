import EremenkosConjecture.RayCounterexampleCriterion

/-! # Dynamical conclusion for an arbitrary continuum

This is the final implication in the proof of Theorem 1.2. The analytic
construction must provide every field below, including the barriers and
uniform escape on the whole continuum. No existence of these data is asserted.
-/

open Set Metric Function Filter ComplexDynamics
open scoped Topology

namespace EremenkosConjecture

open Scaffolding

/-- Construction data for the general-continuum version of Section 7.
The sets may be decorated halfstrips; no straight-strip geometry is imposed. -/
structure ContinuumConstructionData (f : ℂ → ℂ) (X : Set ℂ) (ζ : ℂ) : Prop where
  entire : IsEntire f
  connected : IsConnected X
  base_mem : ζ ∈ X
  barriers : ∃ B : ℕ → Set ℂ,
    (∀ j, IsClosed (B j)) ∧
    (∀ j, X ∪ horizontalRay ζ ⊆ interior (B j)) ∧
    (⋂ j, B j) = X ∪ horizontalRay ζ ∧
    (∀ j, MapsTo (f^[returnTime j + 1]) (frontier (B j)) trappingDisk) ∧
    ∃ u : ℕ → ℂ, (∀ n, u n ∈ frontier (B 0)) ∧
      Tendsto (fun n => ‖u n‖) atTop atTop
  trapping : MapsTo f trappingDisk (ball 0 (1 / 2))
  excursions : ∀ j, MapsTo (f^[returnTime j]) (X ∪ horizontalRay ζ) (targetStrip j)
  returns : ∀ j, MapsTo (f^[returnTime j + 1]) (X ∪ horizontalRay ζ) (sourceStrip 0)
  boundedReturns : ∀ z ∈ (X ∪ horizontalRay ζ) \ X,
    ∀ᶠ j in atTop, |((f^[returnTime j + 1]) z).re| ≤ 1
  escape : ∀ z ∈ X, ∀ j n, returnTime j + 1 ≤ n → n ≤ returnTime (j + 1) →
    (j : ℝ) ≤ |((f^[n]) z).re|

theorem ContinuumConstructionData.continuum_escapes {f : ℂ → ℂ}
    {X : Set ℂ} {ζ : ℂ} (D : ContinuumConstructionData f X ζ) : X ⊆ escapingSet f :=
  fun z hz => mem_escapingSet_of_return_blocks (D.escape z hz)

theorem ContinuumConstructionData.remainder_bungee {f : ℂ → ℂ}
    {X : Set ℂ} {ζ : ℂ} (D : ContinuumConstructionData f X ζ) :
    (X ∪ horizontalRay ζ) \ X ⊆ bungeeSet f := by
  intro z hz
  exact mem_bungeeSet_of_strip_returns (fun j => D.excursions j hz.1)
    (fun j => D.returns j hz.1) (D.boundedReturns z hz)

/-- Once the analytic data exist, the prescribed continuum is an actual
connected escaping component, not just a path component. -/
theorem ContinuumConstructionData.conclusions {f : ℂ → ℂ}
    {X : Set ℂ} {ζ : ℂ} (D : ContinuumConstructionData f X ζ) :
    IsTranscendentalEntire f ∧ X ⊆ escapingSet f ∧
      (X ∪ horizontalRay ζ) \ X ⊆ bungeeSet f ∧
      connectedComponentIn (escapingSet f ∪ bungeeSet f) ζ = X ∪ horizontalRay ζ ∧
      connectedComponentIn (escapingSet f) ζ = X := by
  obtain ⟨B, hB, hinside, hinter, hboundary, u, hu, huinfty⟩ := D.barriers
  let K := X ∪ horizontalRay ζ
  have hζK : ζ ∈ K := Or.inl D.base_mem
  have hζI : ζ ∈ escapingSet f := D.continuum_escapes D.base_mem
  have hKconn : IsConnected K := D.connected.union
    ⟨ζ, D.base_mem, mem_horizontalRay ζ⟩ (isConnected_horizontalRay ζ)
  have hKA : K ⊆ escapingSet f ∪ bungeeSet f := by
    intro z hz
    by_cases hzX : z ∈ X
    · exact Or.inl (D.continuum_escapes hzX)
    · exact Or.inr (D.remainder_bungee ⟨hz, hzX⟩)
  have htrap : MapsTo f trappingDisk trappingDisk :=
    D.trapping.mono_right ball_subset_closedBall
  have hbounded : ∀ j, frontier (B j) ⊆ boundedOrbitSet f := by
    intro j z hz
    exact trappedSet_subset_boundedOrbitSet isBounded_closedBall
      (mem_trappedSet_of_iterate_mem htrap (hboundary j hz))
  have hdisj : ∀ j, Disjoint (escapingSet f ∪ bungeeSet f) (frontier (B j)) := by
    intro j
    apply disjoint_left.mpr
    intro z hz hzB
    rcases hz with hI | hBU
    · exact disjoint_left.mp (disjoint_boundedOrbitSet_escapingSet f) (hbounded j hzB) hI
    · exact (mem_bungeeSet_iff.mp hBU).1 (hbounded j hzB)
  have hcomponent : connectedComponentIn (escapingSet f ∪ bungeeSet f) ζ = K :=
    connectedComponentIn_eq_of_closed_barriers hKconn.isPreconnected hKA hB hinside
      hinter hdisj hζK
  have hXcomponent : connectedComponentIn (escapingSet f) ζ = X := by
    apply Subset.antisymm
    · intro z hz
      have hzK : z ∈ K := by
        change z ∈ X ∪ horizontalRay ζ
        rw [← hinter]
        exact mem_iInter.mpr fun j => interior_subset
          (connectedComponentIn_subset_interior_of_frontier_disjoint (hB j)
            ((hdisj j).mono_left subset_union_left) hζI (hinside j hζK) hz)
      by_contra hzX
      exact (mem_bungeeSet_iff.mp (D.remainder_bungee ⟨hzK, hzX⟩)).2
        (connectedComponentIn_subset (escapingSet f) ζ hz)
    · exact D.connected.isPreconnected.subset_connectedComponentIn D.base_mem D.continuum_escapes
  have htrans : IsTranscendentalEntire f :=
    isTranscendentalEntire_of_escape_and_bounded_values D.entire hζI u huinfty
      (1 / 2) (fun n => by
        have H := hboundary 0 (hu n)
        simpa only [returnTime_zero, zero_add, iterate_one, trappingDisk,
          mem_closedBall, dist_zero_right] using H)
  exact ⟨htrans, D.continuum_escapes, D.remainder_bungee, hcomponent, hXcomponent⟩

end EremenkosConjecture
