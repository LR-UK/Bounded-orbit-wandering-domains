import EremenkosConjecture.ContinuumCounterexampleCriterion
import ComplexDynamics.UniformEscape

/-! # Uniform escape and Julia boundaries for the continuum construction

These are consequences of the explicit construction data for Theorem 1.2.
The existence of the analytic construction remains a separate obligation.
-/

open Set Metric Function Filter ComplexDynamics
open scoped Topology

namespace EremenkosConjecture

open Scaffolding

theorem ContinuumConstructionData.escapesUniformlyOn {f : ℂ → ℂ}
    {X : Set ℂ} {ζ : ℂ} (D : ContinuumConstructionData f X ζ) :
    EscapesUniformlyOn f X := by
  intro R
  obtain ⟨J, hJ⟩ := exists_nat_gt R
  filter_upwards [eventually_ge_atTop (returnTime J + 1)] with n hn
  obtain ⟨j, hjlo, hjhi⟩ := exists_returnTime_interval (by omega : 1 ≤ n)
  have hJj : J ≤ j := by
    by_contra h
    have hle := strictMono_returnTime.monotone (show j + 1 ≤ J by omega)
    omega
  have hcast : (J : ℝ) ≤ (j : ℝ) := by exact_mod_cast hJj
  intro z hz
  exact (hJ.trans_le hcast).trans_le
    ((D.escape z hz j n hjlo hjhi).trans (Complex.abs_re_le_norm _))

theorem ContinuumConstructionData.interior_subset_fatouSet {f : ℂ → ℂ}
    {X : Set ℂ} {ζ : ℂ} (D : ContinuumConstructionData f X ζ) :
    interior X ⊆ fatouSet f :=
  D.escapesUniformlyOn.interior_subset_fatouSet

theorem ContinuumConstructionData.frontier_union_ray_subset_juliaSet {f : ℂ → ℂ}
    {X : Set ℂ} {ζ : ℂ} (D : ContinuumConstructionData f X ζ) :
    frontier (X ∪ horizontalRay ζ) ⊆ juliaSet f := by
  obtain ⟨B, hB, hinside, hinter, hboundary, _⟩ := D.barriers
  have hclosed : IsClosed (X ∪ horizontalRay ζ) := hinter ▸ isClosed_iInter hB
  have htrap : MapsTo f trappingDisk trappingDisk :=
    D.trapping.mono_right ball_subset_closedBall
  have htrapped : ∀ j, frontier (B j) ⊆ trappedSet f trappingDisk :=
    fun j _ hz => mem_trappedSet_of_iterate_mem htrap (hboundary j hz)
  have hclosure : frontier (X ∪ horizontalRay ζ) ⊆ closure (trappedSet f trappingDisk) :=
    (frontier_subset_closure_union_frontiers hclosed B hB
      (fun j => (hinside j).trans interior_subset) hinter).trans
      (closure_mono (iUnion_subset htrapped))
  intro z hz
  have hzK : z ∈ X ∪ horizontalRay ζ := hclosed.closure_eq ▸ hz.1
  exact mem_juliaSet_of_escape_subsequence_of_closure_trappedSet D.entire.continuous
    (isCompact_closedBall 0 (1 / 2)) strictMono_returnTime
    (tendsto_norm_of_targetStrip_excursions (fun j => D.excursions j hzK)) (hclosure hz)

theorem ContinuumConstructionData.frontier_subset_juliaSet {f : ℂ → ℂ}
    {X : Set ℂ} {ζ : ℂ} (D : ContinuumConstructionData f X ζ) (hX : IsClosed X) :
    frontier X ⊆ juliaSet f := by
  have hr : interior (horizontalRay ζ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hzF : z ∈ frontier (horizontalRay ζ) :=
      (frontier_horizontalRay ζ).symm ▸ interior_subset hz
    exact hzF.2 hz
  apply Subset.trans ?_ D.frontier_union_ray_subset_juliaSet
  intro z hz
  refine ⟨subset_closure (Or.inl (hX.closure_eq ▸ hz.1)), ?_⟩
  rw [interior_union_isClosed_of_interior_empty hX hr]
  exact hz.2

theorem ContinuumConstructionData.component_julia_escaping_bungee {f : ℂ → ℂ}
    {X : Set ℂ} {ζ : ℂ} (D : ContinuumConstructionData f X ζ) :
    connectedComponentIn (juliaSet f ∪ escapingSet f ∪ bungeeSet f) ζ =
      X ∪ horizontalRay ζ := by
  obtain ⟨B, hB, hinside, hinter, hboundary, _⟩ := D.barriers
  have htrap : MapsTo f trappingDisk trappingDisk :=
    D.trapping.mono_right ball_subset_closedBall
  have hbounded : ∀ j, frontier (B j) ⊆ boundedOrbitSet f := by
    intro j z hz
    exact trappedSet_subset_boundedOrbitSet isBounded_closedBall
      (mem_trappedSet_of_iterate_mem htrap (hboundary j hz))
  have hfatou : ∀ j, frontier (B j) ⊆ fatouSet f := by
    intro j z hz
    have hentry : (f^[returnTime j + 1 + 1]) z ∈ ball 0 (1 / 2) := by
      rw [iterate_succ_apply']
      exact D.trapping (hboundary j hz)
    exact mem_fatouSet_of_iterate_mem_bounded_invariant D.entire isOpen_ball isBounded_ball
      (D.trapping.mono_left ball_subset_closedBall) hentry
  have hdisj : ∀ j, Disjoint (juliaSet f ∪ escapingSet f ∪ bungeeSet f) (frontier (B j)) := by
    intro j
    apply disjoint_left.mpr
    intro z hz hzB
    rcases hz with (hJ | hI) | hBU
    · exact hJ (hfatou j hzB)
    · exact disjoint_left.mp (disjoint_boundedOrbitSet_escapingSet f) (hbounded j hzB) hI
    · exact (mem_bungeeSet_iff.mp hBU).1 (hbounded j hzB)
  apply connectedComponentIn_eq_of_closed_barriers
    (D.connected.union ⟨ζ, D.base_mem, mem_horizontalRay ζ⟩
      (isConnected_horizontalRay ζ)).isPreconnected ?_ hB hinside hinter hdisj
      (Or.inl D.base_mem)
  intro z hz
  by_cases hzX : z ∈ X
  · exact Or.inl (Or.inr (D.continuum_escapes hzX))
  · exact Or.inr (D.remainder_bungee ⟨hz, hzX⟩)

end EremenkosConjecture
