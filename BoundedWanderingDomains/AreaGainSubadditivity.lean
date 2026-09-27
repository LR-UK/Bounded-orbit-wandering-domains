/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# Subadditivity of area gains

Inserting auxiliary punctures is useful because it gives the old domain
fixed omitted values. The area gain from removing two sets is at most the
gain after inserting the auxiliary punctures plus their insertion cost.
-/

open MeasureTheory
open scoped ENNReal

namespace AreaDeficit

/-- An elementary integral inequality for area gains. No total-area
finiteness is required; the second gain need only be measurable. -/
theorem lintegral_gain_le_gain_add_gain
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g h k : α → ℝ≥0∞)
    (hfg : f ≤ᵐ[μ] g) (hgh : AEMeasurable (fun x => g x - h x) μ) :
    (∫⁻ x, f x - k x ∂μ) ≤
      (∫⁻ x, g x - h x ∂μ) + (∫⁻ x, h x - k x ∂μ) := by
  calc
    (∫⁻ x, f x - k x ∂μ) ≤
        ∫⁻ x, (g x - h x) + (h x - k x) ∂μ := by
          apply lintegral_mono_ae
          filter_upwards [hfg] with x hx
          exact (tsub_le_tsub_right hx _).trans tsub_le_tsub_add_tsub
    _ = (∫⁻ x, g x - h x ∂μ) +
          (∫⁻ x, h x - k x ∂μ) := lintegral_add_left' hgh _

end AreaDeficit
