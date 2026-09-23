/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.CoveringCutoffArea
import BoundedWanderingDomains.CutoffAreaLimit

open Set Filter MeasureTheory InnerProductSpace Laplacian Metric
open scoped Topology ContDiff ENNReal

namespace AreaDeficit

/-- The normalised hyperbolic area of the finitely punctured plane. -/
theorem IsHolomorphicDiscCovering.total_area {P : Finset ℂ} {p : ℂ → ℂ}
    (hp : IsHolomorphicDiscCovering p (↑P : Set ℂ)ᶜ) (hP : 2 ≤ P.card) :
    (∫⁻ z : ℂ, ENNReal.ofReal ((coveringDensity p z)^2 / (2 * Real.pi))) =
      (P.card - 1 : ℕ) := by
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < P.card)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_cutoffSeparated P c)
  let u : ℕ → ℝ := fun n => (n : ℝ) + T
  have hu : Tendsto u atTop atTop :=
    tendsto_atTop_add_const_right atTop T tendsto_natCast_atTop_atTop
  have hs (n : ℕ) : CutoffSeparated P c (u n) := hT (u n) (by dsimp [u]; linarith [Nat.cast_nonneg (α := ℝ) n])
  let F : ℕ → ℂ → ℝ := fun n z =>
    (puncturedCutoff P c (u n) z * (coveringDensity p z)^2) / (2 * Real.pi)
  have hi (n : ℕ) : Integrable (F n) :=
    (hp.integrable_cutoff_density (hs n)).div_const _
  have hpos (n : ℕ) (z : ℂ) : 0 ≤ F n z := by
    dsimp [F]
    exact div_nonneg (mul_nonneg (puncturedCutoff_bounds (hs n)).1 (sq_nonneg _)) (by positivity)
  have hle (n : ℕ) (z : ℂ) : F n z ≤ (coveringDensity p z)^2 / (2 * Real.pi) := by
    dsimp [F]
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (puncturedCutoff_bounds (hs n)).2 (sq_nonneg (coveringDensity p z))
  have hpoint : ∀ᵐ z : ℂ, Tendsto (fun n => F n z) atTop
      (𝓝 ((coveringDensity p z)^2 / (2 * Real.pi))) := by
    have hnull : ∀ᵐ z : ℂ, z ∉ P := by
      rw [ae_iff]
      simp only [not_not]
      exact P.finite_toSet.measure_zero volume
    filter_upwards [hnull] with z hz
    apply tendsto_const_nhds.congr'
    filter_upwards [hu.eventually (puncturedCutoff_eventually_one P c hz)] with n hn
    simp [F, hn]
  have hint : Tendsto (fun n => ∫ z : ℂ, F n z) atTop (𝓝 ((P.card : ℝ) - 1)) := by
    have h := ((hp.tendsto_cutoff_area hP hc).comp hu).div_const (2 * Real.pi)
    have he : 2 * Real.pi * ((P.card : ℝ) - 1) / (2 * Real.pi) = (P.card : ℝ) - 1 := by
      field_simp
    simpa only [F, integral_div, he, Function.comp_def] using h
  have h := lintegral_eq_of_cutoff_integrals hi hpos hle hpoint hint
  have he : ((P.card - 1 : ℕ) : ℝ) = (P.card : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ P.card), Nat.cast_one]
  rw [← he] at h
  simpa using h

end AreaDeficit

#print axioms AreaDeficit.IsHolomorphicDiscCovering.total_area
