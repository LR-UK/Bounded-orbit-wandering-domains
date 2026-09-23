import BoundedWanderingDomains.AreaCancellation

open Set MeasureTheory
open scoped ENNReal

namespace AreaDeficit

/-- Monotonicity and a total finite-area bound control the area increase
on every measurable subset. For punctured spheres the outstanding input
is the geometric total-area formula (Gauss–Bonnet). -/
theorem area_cost_on_set_of_total_cost {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} {B : Set α} {D : ℝ≥0∞}
    (hB : MeasurableSet B) (hμν : μ ≤ ν) (hfinite : μ univ ≠ ∞)
    (htotal : ν univ ≤ μ univ + D) : ν B ≤ μ B + D := by
  have hcomp : μ Bᶜ ≠ ∞ := ne_top_of_le_ne_top hfinite (measure_mono (subset_univ _))
  apply (ENNReal.add_le_add_iff_right hcomp).mp
  calc
    ν B + μ Bᶜ ≤ ν B + ν Bᶜ := by gcongr
    _ = ν univ := measure_add_measure_compl hB
    _ ≤ μ univ + D := htotal
    _ = (μ B + D) + μ Bᶜ := by rw [← measure_add_measure_compl hB]; ac_rfl

end AreaDeficit
