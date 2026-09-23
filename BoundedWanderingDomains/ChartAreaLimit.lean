import BoundedWanderingDomains.InteriorDensityLimit
import BoundedWanderingDomains.LocalIntegratedDeficit
import BoundedWanderingDomains.DiscArea

open Set Metric Function Filter MeasureTheory
open scoped Topology ENNReal

namespace AreaDeficit.FinitePunctureMetricInput

theorem square_area_eq_scaled_area (G : FinitePunctureMetricInput) (P : Finset ℂ) :
    volume.withDensity (fun z => ENNReal.ofReal ((G.density P z)^2)) =
      ENNReal.ofReal (2 * Real.pi) • G.area P := by
  rw [area, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- The proved density limit and Fatou transfer a uniform punctured-area
bound to the intrinsic area expressed in a conformal chart. -/
theorem chart_area_bound (G : FinitePunctureMetricInput)
    {P : ℕ → Finset ℂ} (hP : Monotone P)
    {a b z : ℂ} (hab : a ≠ b) (ha : a ∈ P 0) (hb : b ∈ P 0)
    {u : ℂ → ℂ} {B : Set ℂ} {H : ℝ≥0∞}
    (hu : DifferentiableOn ℂ u (connectedComponentIn
      (closure (⋃ n, (↑(P n) : Set ℂ)))ᶜ z))
    (hum : MapsTo u (connectedComponentIn
      (closure (⋃ n, (↑(P n) : Set ℂ)))ᶜ z) (ball 0 1))
    (hB : MeasurableSet B)
    (hBU : B ⊆ connectedComponentIn (closure (⋃ n, (↑(P n) : Set ℂ)))ᶜ z)
    (hbound : ∀ n, G.area (P n) B ≤ H) :
    (∫⁻ x in B, ENNReal.ofReal ((‖deriv u x‖ * discDensity (u x))^2)) ≤
      ENNReal.ofReal (2 * Real.pi) * H := by
  have hc : ∀ n, 2 ≤ (P n).card := fun n => Finset.one_lt_card.mpr
    ⟨a, hP (Nat.zero_le n) ha, b, hP (Nat.zero_le n) hb, hab⟩
  have hw : ∀ n, Measurable (fun x => ENNReal.ofReal ((G.density (P n) x)^2)) :=
    fun n => ((G.measurable_density (hc n)).pow_const 2).ennreal_ofReal
  calc
    _ ≤ ∫⁻ x in B, liminf (fun n => ENNReal.ofReal ((G.density (P n) x)^2)) atTop := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hB] with x hx
      have hxU := hBU hx
      have hcomp := connectedComponentIn_eq hxU
      obtain ⟨ell, hell, ht, hl⟩ := G.density_limit_lower hP hab ha hb
        (connectedComponentIn_subset _ _ hxU)
        (by simpa only [hcomp] using hu) (by simpa only [hcomp] using hum)
      have hlim : Tendsto (fun n => ENNReal.ofReal ((G.density (P n) x)^2)) atTop
          (𝓝 (ENNReal.ofReal (ell^2))) := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (ht.pow 2)
      rw [hlim.liminf_eq]
      apply ENNReal.ofReal_le_ofReal
      have hnorm : ‖u x‖ < 1 := mem_ball_zero_iff.mp (hum hxU)
      have hpos : 0 ≤ discDensity (u x) := by
        unfold discDensity discDenom
        rw [Complex.normSq_eq_norm_sq]
        apply div_nonneg (by norm_num)
        nlinarith [norm_nonneg (u x)]
      nlinarith [mul_nonneg hpos (norm_nonneg (deriv u x))]
    _ ≤ liminf (fun n => ∫⁻ x in B, ENNReal.ofReal ((G.density (P n) x)^2)) atTop :=
      lintegral_liminf_le' (fun n => (hw n).aemeasurable)
    _ ≤ ENNReal.ofReal (2 * Real.pi) * H := by
      apply liminf_le_of_frequently_le' (Frequently.of_forall ?_)
      intro n
      rw [← withDensity_apply _ hB, G.square_area_eq_scaled_area, Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul_right (hbound n) _

end AreaDeficit.FinitePunctureMetricInput

namespace AreaDeficit

/-- The intrinsic disc area in any holomorphic bijective chart. No
hyperbolic uniformisation theorem is assumed here. -/
theorem chart_disc_area {u : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) (hbij : BijOn u U (ball 0 1))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    (∫⁻ x in U ∩ u ⁻¹' ball 0 r, ENNReal.ofReal ((‖deriv u x‖ * discDensity (u x))^2)) =
      ENNReal.ofReal (4 * Real.pi * r^2 / (1 - r^2)) := by
  have hB : MeasurableSet (U ∩ u ⁻¹' ball 0 r) :=
    (hu.continuousOn.isOpen_inter_preimage hU isOpen_ball).measurableSet
  have himage : u '' (U ∩ u ⁻¹' ball 0 r) = ball 0 r := by
    apply Subset.antisymm
    · rintro y ⟨x, ⟨_, hx⟩, rfl⟩
      exact hx
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := hbij.surjOn ((ball_subset_ball hr1.le) hy)
      exact ⟨x, ⟨hx, by simpa only [mem_preimage, hxy] using hy⟩, hxy⟩
  have h := holomorphic_change_of_variables hB
    (fun z hz => hu.hasDerivAt (hU.mem_nhds hz.1)) (hbij.injOn.mono inter_subset_left)
    (fun z => ENNReal.ofReal ((discDensity z)^2))
  rw [himage] at h
  rw [← disc_area_lintegral hr hr1, h]
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_mul (sq_nonneg _), mul_pow]

end AreaDeficit

#print axioms AreaDeficit.FinitePunctureMetricInput.chart_area_bound
#print axioms AreaDeficit.chart_disc_area
