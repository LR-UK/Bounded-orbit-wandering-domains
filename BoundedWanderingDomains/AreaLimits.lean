import BoundedWanderingDomains.AreaCancellation
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace AreaDeficit

/-- Compact containment gives the finite area needed for cancellation for
each continuous density separately. No uniform upper bound is required. -/
theorem finite_weighted_area_of_compact {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [T2Space α]
    {m : Measure α} [IsLocallyFiniteMeasure m]
    {K W : Set α} {w : α → ℝ}
    (hK : IsCompact K) (hWK : W ⊆ K) (hw : ContinuousOn w K)
    (hpos : ∀ x ∈ K, 0 ≤ w x) :
    m.withDensity (fun x => ENNReal.ofReal (w x)) W ≠ ∞ := by
  have hi : IntegrableOn w K m := hw.integrableOn_compact hK
  have hn : ∀ᵐ x ∂m.restrict K, 0 ≤ w x :=
    (ae_restrict_mem hK.measurableSet).mono hpos
  have hf : (∫⁻ x in K, ENNReal.ofReal (w x) ∂m) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable hn).mpr hi
  rw [← withDensity_apply _ hK.measurableSet] at hf
  exact ne_top_of_le_ne_top hf (measure_mono hWK)

/-- Fatou transfers a uniform bound to the intrinsic limiting density.
Monotonicity of the approximations is not needed. -/
theorem limiting_area_bound {α : Type*} [MeasurableSpace α]
    {m : Measure α} {B : Set α} {w : ℕ → α → ℝ≥0∞} {v : α → ℝ≥0∞}
    {K : ℝ≥0∞} (hw : ∀ n, AEMeasurable (w n) (m.restrict B))
    (hlim : ∀ᵐ x ∂m.restrict B, Tendsto (fun n => w n x) atTop (𝓝 (v x)))
    (hbound : ∀ n, (∫⁻ x in B, w n x ∂m) ≤ K) :
    (∫⁻ x in B, v x ∂m) ≤ K := by
  calc
    (∫⁻ x in B, v x ∂m) = ∫⁻ x in B, liminf (fun n => w n x) atTop ∂m := by
      apply lintegral_congr_ae
      filter_upwards [hlim] with x hx
      exact hx.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x in B, w n x ∂m) atTop := lintegral_liminf_le' hw
    _ ≤ K := liminf_le_of_frequently_le' (Frequently.of_forall hbound)

/-- A family of discs may use different tails, initial sets, and even maps.
Only the two error constants must be uniform in the family parameter.
Unbounded limiting areas then contradict cancellation. The theorem does
not assert the geometric existence of such discs or metric limits. -/
theorem no_unbounded_limiting_wandering_areas
    {α ι : Type*} [MeasurableSpace α] {m : Measure α}
    {f : ι → α → α} {B : ι → Set α}
    {w : ι → ℕ → α → ℝ≥0∞} {v : ι → α → ℝ≥0∞}
    {ν : ι → ℕ → Measure α} {C D : ℝ≥0∞}
    (hC : C ≠ ∞) (hD : D ≠ ∞)
    (hB : ∀ i, MeasurableSet (B i))
    (hwand : ∀ i, HasDisjointForwardImages (f i) (B i))
    (hw : ∀ i n, AEMeasurable (w i n) (m.restrict (B i)))
    (hfinite : ∀ i n, m.withDensity (w i n) (forwardOrbit (f i) (B i)) ≠ ∞)
    (hadvance : ∀ i n, m.withDensity (w i n) (forwardOrbit (f i) (B i)) ≤
      ν i n (f i '' forwardOrbit (f i) (B i)) + C)
    (hcost : ∀ i n, ν i n (f i '' forwardOrbit (f i) (B i)) ≤
      m.withDensity (w i n) (f i '' forwardOrbit (f i) (B i)) + D)
    (hlim : ∀ i, ∀ᵐ x ∂m.restrict (B i),
      Tendsto (fun n => w i n x) atTop (𝓝 (v i x)))
    (hunbounded : ∀ K : ℝ≥0∞, K ≠ ∞ → ∃ i, K < ∫⁻ x in B i, v i x ∂m) :
    False := by
  obtain ⟨i, hi⟩ := hunbounded (D + C) (ENNReal.add_ne_top.mpr ⟨hD, hC⟩)
  apply (not_lt_of_ge (limiting_area_bound (hw i) (hlim i) ?_)) hi
  intro n
  rw [← withDensity_apply _ (hB i)]
  exact wandering_area_bound (hB i) (hwand i) (hfinite i n) (hadvance i n) (hcost i n)

end AreaDeficit
