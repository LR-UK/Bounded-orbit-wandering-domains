import WanderingSets
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace AreaDeficit

/-- Cancellation is valid because the area of the forward union is finite.
The two geometric area comparisons are exposed separately. -/
theorem finite_area_cancellation {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} {f : α → α} {B W : Set α} {C D : ℝ≥0∞}
    (hB : MeasurableSet B) (hBW : B ⊆ W) (hfinite : μ W ≠ ∞)
    (himage : f '' W ⊆ W \ B)
    (hadvance : μ W ≤ ν (f '' W) + C)
    (hcost : ν (f '' W) ≤ μ (f '' W) + D) : μ B ≤ D + C := by
  have hrem : μ (W \ B) ≠ ∞ := ne_top_of_le_ne_top hfinite (measure_mono sdiff_subset)
  have hsplit : μ B + μ (W \ B) = μ W := by
    simpa only [inter_eq_right.mpr hBW] using measure_inter_add_sdiff W hB
  have hh : μ B + μ (W \ B) ≤ (D + C) + μ (W \ B) := by
    calc
      μ B + μ (W \ B) = μ W := hsplit
      _ ≤ ν (f '' W) + C := hadvance
      _ ≤ (μ (f '' W) + D) + C := by gcongr
      _ ≤ (μ (W \ B) + D) + C := by gcongr
      _ = (D + C) + μ (W \ B) := by ac_rfl
  exact (ENNReal.add_le_add_iff_right hrem).mp hh

theorem wandering_area_bound {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} {f : α → α} {B : Set α} {C D : ℝ≥0∞}
    (hB : MeasurableSet B) (hw : HasDisjointForwardImages f B)
    (hfinite : μ (forwardOrbit f B) ≠ ∞)
    (hadvance : μ (forwardOrbit f B) ≤ ν (f '' forwardOrbit f B) + C)
    (hcost : ν (f '' forwardOrbit f B) ≤ μ (f '' forwardOrbit f B) + D) :
    μ B ≤ D + C :=
  finite_area_cancellation hB (subset_forwardOrbit f B) hfinite
    (image_forwardOrbit_eq_sdiff hw).subset hadvance hcost

/-- Uniformly bounded density integrals cannot diverge pointwise to infinity
on a set of positive reference measure. This uses Fatou, not integrability
of a putative limiting density. -/
theorem measure_zero_of_density_blowup {α : Type*} [MeasurableSpace α]
    {m : Measure α} {B : Set α} {w : ℕ → α → ℝ≥0∞} {K : ℝ≥0∞}
    (hK : K ≠ ∞) (hw : ∀ n, AEMeasurable (w n) (m.restrict B))
    (hlim : ∀ᵐ x ∂m.restrict B, Tendsto (fun n => w n x) atTop (𝓝 ∞))
    (hbound : ∀ n, (∫⁻ x in B, w n x ∂m) ≤ K) : m B = 0 := by
  have hfatou : (∫⁻ _x in B, (∞ : ℝ≥0∞) ∂m) ≤ K := by
    calc
      (∫⁻ _x in B, (∞ : ℝ≥0∞) ∂m) =
          ∫⁻ x in B, liminf (fun n => w n x) atTop ∂m := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with x hx
        exact hx.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x in B, w n x ∂m) atTop := lintegral_liminf_le' hw
      _ ≤ K := liminf_le_of_frequently_le' (Frequently.of_forall hbound)
  by_contra hB
  have ht : (∫⁻ _x in B, (∞ : ℝ≥0∞) ∂m) = ∞ := by simp [hB]
  exact hK (top_unique (ht ▸ hfatou))

/-- The measure-theoretic end of the positive-area argument. The analytic
area comparison, puncture cost, and density blowup remain explicit inputs. -/
theorem null_wandering_set_of_density_data {α : Type*} [MeasurableSpace α]
    {m : Measure α} {f : α → α} {B : Set α}
    {w : ℕ → α → ℝ≥0∞} {ν : ℕ → Measure α} {C D : ℝ≥0∞}
    (hB : MeasurableSet B) (hwand : HasDisjointForwardImages f B)
    (hC : C ≠ ∞) (hD : D ≠ ∞)
    (hw : ∀ n, AEMeasurable (w n) (m.restrict B))
    (hfinite : ∀ n, m.withDensity (w n) (forwardOrbit f B) ≠ ∞)
    (hadvance : ∀ n, m.withDensity (w n) (forwardOrbit f B) ≤
      ν n (f '' forwardOrbit f B) + C)
    (hcost : ∀ n, ν n (f '' forwardOrbit f B) ≤
      m.withDensity (w n) (f '' forwardOrbit f B) + D)
    (hlim : ∀ᵐ x ∂m.restrict B, Tendsto (fun n => w n x) atTop (𝓝 ∞)) :
    m B = 0 := by
  apply measure_zero_of_density_blowup (ENNReal.add_ne_top.mpr ⟨hD, hC⟩) hw hlim
  intro n
  rw [← withDensity_apply _ hB]
  exact wandering_area_bound hB hwand (hfinite n) (hadvance n) (hcost n)

end AreaDeficit
