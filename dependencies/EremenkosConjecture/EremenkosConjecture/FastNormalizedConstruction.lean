import EremenkosConjecture.NonemptyBoundaryData
import EremenkosConjecture.VariableDynamics
import EremenkosConjecture.NormalizedConstruction

/-! # Fast wandering compacta in the unit disk -/

open Set Metric Function ComplexDynamics

namespace EremenkosConjecture

/-- A uniform wandering construction with an explicit fast-escape radius
and a Julia boundary point witnessing that this radius is permitted. -/
structure FastWanderingWitness (K : Set ℂ) extends UniformWanderingWitness K where
  radius : ℝ
  radius_pos : 0 < radius
  fastAt : ∀ r : ℝ, 0 ≤ r → K ⊆ fastEscapingSetAtRadius f r
  marker : ℂ
  marker_boundary : marker ∈ frontier K
  marker_norm : ‖marker‖ < radius

theorem FastWanderingWitness.fast {K : Set ℂ} (W : FastWanderingWitness K)
    (hK : IsClosed K) : K ⊆ fastEscapingSet W.f := by
  intro z hz
  refine ⟨W.radius, W.radius_pos, ⟨W.marker, ?_,
    W.toUniformWanderingWitness.julia_boundary hK W.marker_boundary⟩,
    W.fastAt W.radius W.radius_pos.le hz⟩
  simpa only [mem_ball, dist_zero_right] using W.marker_norm

theorem exists_fastWanderingWitness_normalized (K : Set ℂ) (hK : IsCompact K)
    (hfull : IsConnected Kᶜ) (hne : K.Nonempty) (hnorm : K ⊆ targetDisc 0) :
    Nonempty (FastWanderingWitness K) := by
  obtain ⟨D, hKD, _, hboundary, hPne⟩ := exists_uniformEscapeData_nonempty K hK hfull hne hnorm
  obtain ⟨V⟩ := VariableConstruction.exists_entireConstruction D
  have hmapK (n : ℕ) : MapsTo (V.f^[n]) K (V.chain.target n) :=
    fun z hz => V.maps_target n (hKD n hz)
  have hdisjoint : ∀ n m : ℕ, n ≠ m → Disjoint ((V.f^[n]) '' K) ((V.f^[m]) '' K) :=
    fun n m hnm => (V.chain.disjoint_targets hnm).mono (hmapK n).image_subset (hmapK m).image_subset
  have htrapSub : trappingDisc ⊆ controlDisc 0 := by
    simpa only [controlDisc, trappingDisc, Nat.cast_zero, mul_zero, add_zero] using
      (ball_subset_closedBall : ball (-3 : ℂ) 1 ⊆ closedBall (-3) 1)
  have hforward : MapsTo V.f (controlDisc 0) (controlDisc 0) :=
    fun z hz => htrapSub ((V.property 0).1 hz)
  have hP : (⋃ n, D.P n) ⊆ trappedSet V.f (controlDisc 0) := by
    intro z hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp hz
    exact mem_trappedSet_of_iterate_mem hforward (htrapSub (V.maps_points n hn))
  have hfront : (frontier K).Nonempty := nonempty_frontier_iff.mpr ⟨hne, by
    intro heq
    have H := hfull.nonempty
    simpa [heq] using H⟩
  obtain ⟨a, ha⟩ := hfront
  have haK : a ∈ K := (frontier_subset_iff_isClosed.mpr hK.isClosed) ha
  have hanorm : ‖a‖ < 1 := by simpa [targetDisc] using hnorm haK
  have hr := V.chain.radius_lower 1
  norm_num at hr
  refine ⟨{
    f := V.f
    transcendental := V.transcendental hKD hne hPne
    B := controlDisc 0
    compactB := isCompact_closedBall _ _
    escape := V.escapesUniformly hKD
    disjoint := hdisjoint
    boundary := hboundary.trans (closure_mono hP)
    ambient := ?_
    radius := V.chain.radius 1 - 3
    radius_pos := by linarith
    fastAt := V.fastEscapeAtEveryRadius hKD
    marker := a
    marker_boundary := ha
    marker_norm := by linarith
  }⟩
  intro n
  obtain ⟨H, U, hU, hDU, heq, hH, hHi⟩ := V.charts n
  exact ⟨H, fun z hz => heq (hDU (hKD n hz))⟩

end EremenkosConjecture
