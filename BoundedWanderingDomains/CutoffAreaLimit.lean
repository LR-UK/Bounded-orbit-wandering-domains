/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace AreaDeficit

/-- Fatou and the pointwise upper bound identify the total mass from cutoff integrals. -/
theorem lintegral_eq_of_cutoff_integrals {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {f : α → ℝ} {C : ℝ}
    (hi : ∀ n, Integrable (F n) μ)
    (hpos : ∀ n x, 0 ≤ F n x) (hle : ∀ n x, F n x ≤ f x)
    (hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hint : Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 C)) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) = ENNReal.ofReal C := by
  have he (n : ℕ) : (∫⁻ x, ENNReal.ofReal (F n x) ∂μ) = ENNReal.ofReal (∫ x, F n x ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (hi n) (ae_of_all _ (hpos n))).symm
  have hlim : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) atTop (𝓝 (ENNReal.ofReal C)) := by
    simp_rw [he]
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hint
  apply le_antisymm
  · calc
      (∫⁻ x, ENNReal.ofReal (f x) ∂μ) =
          ∫⁻ x, liminf (fun n => ENNReal.ofReal (F n x)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hpoint] with x hx
        exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hx).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) atTop :=
        lintegral_liminf_le' (fun n => (hi n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ = ENNReal.ofReal C := hlim.liminf_eq
  · exact le_of_tendsto' hlim (fun n => lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hle n x)))

end AreaDeficit
