/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.GeneralDensityLimit
import BoundedWanderingDomains.ChartAreaLimit
import BoundedWanderingDomains.CoveringAreaTransport

open Set Metric Function Filter MeasureTheory
open scoped Topology ENNReal

namespace AreaDeficit.FinitePunctureMetricInput

/-- Finite-model area bounds pass to the universal-covering metric of an
arbitrary limiting component. -/
theorem covering_area_bound (G : FinitePunctureMetricInput)
    {P : ℕ → Finset ℂ} (hP : Monotone P)
    {a b z : ℂ} (hab : a ≠ b) (ha : a ∈ P 0) (hb : b ∈ P 0)
    {p : ℂ → ℂ} {B : Set ℂ} {H : ℝ≥0∞}
    (hp : IsHolomorphicDiscCovering p (connectedComponentIn
      (closure (⋃ n, (↑(P n) : Set ℂ)))ᶜ z))
    (hB : MeasurableSet B)
    (hBU : B ⊆ connectedComponentIn (closure (⋃ n, (↑(P n) : Set ℂ)))ᶜ z)
    (hbound : ∀ n, G.area (P n) B ≤ H) :
    (∫⁻ x in B, ENNReal.ofReal ((coveringDensity p x)^2)) ≤
      ENNReal.ofReal (2 * Real.pi) * H := by
  have hc : ∀ n, 2 ≤ (P n).card := fun n => Finset.one_lt_card.mpr
    ⟨a, hP (Nat.zero_le n) ha, b, hP (Nat.zero_le n) hb, hab⟩
  have hw : ∀ n, Measurable (fun x => ENNReal.ofReal ((G.density (P n) x)^2)) :=
    fun n => ((G.measurable_density (hc n)).pow_const 2).ennreal_ofReal
  calc
    _ = ∫⁻ x in B, liminf (fun n => ENNReal.ofReal ((G.density (P n) x)^2)) atTop := by
      apply setLIntegral_congr_fun hB
      intro x hx
      have hcomp := connectedComponentIn_eq (hBU hx)
      have ht := G.density_tendsto_component_cover hP hab ha hb
        (connectedComponentIn_subset _ _ (hBU hx)) (by simpa only [hcomp] using hp)
      have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (ht.pow 2)
      exact hlim.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x in B, ENNReal.ofReal ((G.density (P n) x)^2)) atTop :=
      lintegral_liminf_le' (fun n => (hw n).aemeasurable)
    _ ≤ ENNReal.ofReal (2 * Real.pi) * H := by
      apply liminf_le_of_frequently_le' (Frequently.of_forall ?_)
      intro n
      rw [← withDensity_apply _ hB, G.square_area_eq_scaled_area, Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul_right (hbound n) _

end AreaDeficit.FinitePunctureMetricInput
