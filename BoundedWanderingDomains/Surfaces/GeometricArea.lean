/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.AreaCancellation
import Mathlib.MeasureTheory.Measure.Continuity

/-! # Area obstruction for an infinite-area geometric limit

The statements are measure-theoretic, so apply to Riemann surfaces without any
planarity or simple-connectivity assumption. In the intended application, `μ`
is the curvature -1 area on the limiting surface, `K` is an exhaustion, and
`a j n` is the area of the corresponding region at time `n`.

Convergence of these areas is an explicit hypothesis. This file does not assert
that essential thickness implies this convergence or infinite limiting area.
-/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace AreaDeficit.Surfaces

/-- Any finite threshold is eventually exceeded on some fixed member of the
exhaustion. The time may depend on the chosen member and threshold. -/
theorem exists_eventually_large_area
    {M : Type*} [MeasurableSpace M] {μ : Measure M}
    {K : ℕ → Set M} (hK : Monotone K) (hexhaust : (⋃ j, K j) = univ)
    (hinfinite : μ univ = ∞) {a : ℕ → ℕ → ℝ≥0∞}
    (hconverge : ∀ j, Tendsto (a j) atTop (𝓝 (μ (K j))))
    {C : ℝ≥0∞} (hC : C ≠ ∞) :
    ∃ j, ∀ᶠ n in atTop, C < a j n := by
  have hs : (⨆ j, μ (K j)) = ∞ := by
    rw [← hK.measure_iUnion, hexhaust, hinfinite]
  obtain ⟨j, hj⟩ : ∃ j, C < μ (K j) := by
    by_contra h
    push Not at h
    have hle : (⨆ j, μ (K j)) ≤ C := iSup_le h
    rw [hs] at hle
    exact hC (top_unique hle)
  exact ⟨j, (hconverge j).eventually (isOpen_Ioi.mem_nhds hj)⟩

/-- A single finite area bound, even if valid only after a time depending on
the exhaustion member, contradicts convergence to an infinite-area surface. -/
theorem no_uniform_finite_area_bound
    {M : Type*} [MeasurableSpace M] {μ : Measure M}
    {K : ℕ → Set M} (hK : Monotone K) (hexhaust : (⋃ j, K j) = univ)
    (hinfinite : μ univ = ∞) {a : ℕ → ℕ → ℝ≥0∞}
    (hconverge : ∀ j, Tendsto (a j) atTop (𝓝 (μ (K j))))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hbound : ∀ j, ∀ᶠ n in atTop, a j n ≤ C) : False := by
  obtain ⟨j, hj⟩ := exists_eventually_large_area hK hexhaust hinfinite hconverge hC
  obtain ⟨n, hn, hn'⟩ := (hj.and (hbound j)).exists
  exact (not_lt_of_ge hn') hn

end AreaDeficit.Surfaces

#print axioms AreaDeficit.Surfaces.exists_eventually_large_area
#print axioms AreaDeficit.Surfaces.no_uniform_finite_area_bound
