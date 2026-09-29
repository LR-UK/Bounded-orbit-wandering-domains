module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.FinitePunctureArea
public import BoundedWanderingDomains.ChartAreaLimit

@[expose] public section

/-! # Passing finite intrinsic area bounds to a conformal disc -/

open Set Metric Function Filter MeasureTheory
open scoped Topology ENNReal

namespace AreaDeficit

/-- A uniform curvature -1 area bound for finite models controls the area
of a conformal chart of the limiting component. The harmless fixed factor
allows reuse of the original normalised exhaustion lemma. -/
theorem intrinsic_chart_area_bound
    {P : ℕ → Finset ℂ} (hP : Monotone P)
    {a b z : ℂ} (hab : a ≠ b) (ha : a ∈ P 0) (hb : b ∈ P 0)
    {u : ℂ → ℂ} {B : Set ℂ} {H : ℝ≥0∞}
    (hu : DifferentiableOn ℂ u (connectedComponentIn
      (closure (⋃ n, (↑(P n) : Set ℂ)))ᶜ z))
    (hum : MapsTo u (connectedComponentIn
      (closure (⋃ n, (↑(P n) : Set ℂ)))ᶜ z) (ball 0 1))
    (hB : MeasurableSet B)
    (hBU : B ⊆ connectedComponentIn (closure (⋃ n, (↑(P n) : Set ℂ)))ᶜ z)
    (hbound : ∀ n, (∫⁻ x in B,
      hyperbolicAreaWeight (↑(P n) : Set ℂ) (P n).finite_toSet.isClosed hab
        (hP (Nat.zero_le n) ha) (hP (Nat.zero_le n) hb) x) ≤ H) :
    (∫⁻ x in B, ENNReal.ofReal ((‖deriv u x‖ * discDensity (u x))^2)) ≤
      ENNReal.ofReal (2 * Real.pi) * H := by
  let G := canonicalFinitePunctureMetricInput
  apply G.chart_area_bound hP hab ha hb hu hum hB hBU
  intro n
  apply le_trans _ (hbound n)
  rw [FinitePunctureMetricInput.area, withDensity_apply _ hB]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hB] with x hx
  have hxP : x ∉ P n := by
    intro hxP
    exact (connectedComponentIn_subset _ _ (hBU hx))
      (subset_closure (mem_iUnion.mpr ⟨n, hxP⟩))
  rw [G.density_eq_closedComplement (P n) hab
    (hP (Nat.zero_le n) ha) (hP (Nat.zero_le n) hb) hxP]
  apply ENNReal.ofReal_le_ofReal
  exact div_le_self (sq_nonneg _) (by linarith [Real.pi_gt_three])

end AreaDeficit
