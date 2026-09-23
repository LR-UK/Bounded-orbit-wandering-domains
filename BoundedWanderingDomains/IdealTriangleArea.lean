import BoundedWanderingDomains.IdealTriangleIntegral
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure

/-!
# Hyperbolic area of the model ideal triangle

The curvature −1 upper half-plane metric has area density `y⁻²`.
Tonelli's theorem turns the previously evaluated iterated integral into
an actual two-dimensional Lebesgue integral. No triangulation is assumed here.
-/

open Set MeasureTheory Real
open scoped Pointwise ENNReal

namespace AreaDeficit

/-- The open ideal triangle with vertices −1, 1 and ∞. -/
def modelIdealTriangle : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Ioo (-1 : ℝ) 1 ∧ Real.sqrt (1 - z.1^2) < z.2}

theorem measurableSet_modelIdealTriangle : MeasurableSet modelIdealTriangle := by
  unfold modelIdealTriangle
  exact (measurableSet_Ioo.preimage measurable_fst).inter
    (measurableSet_lt (by fun_prop) measurable_snd)

theorem lintegral_upper_halfPlane_vertical {c : ℝ} (hc : 0 < c) :
    (∫⁻ y in Ioi c, ENNReal.ofReal ((y^2)⁻¹)) = ENNReal.ofReal c⁻¹ := by
  have hi : IntegrableOn (fun y : ℝ => (y^2)⁻¹) (Ioi c) := by
    simpa using integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hc
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun y => by positivity)]
  rw [integral_upper_halfPlane_vertical hc]

theorem lintegral_inverse_sqrt_semicircle :
    (∫⁻ x in Ioo (-1 : ℝ) 1, ENNReal.ofReal (1 / Real.sqrt (1 - x^2))) =
      ENNReal.ofReal Real.pi := by
  have hd : ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x^2)) x :=
    fun x hx => Real.hasDerivAt_arcsin (ne_of_gt hx.1) (ne_of_lt hx.2)
  have hi : IntervalIntegrable (fun x : ℝ => 1 / Real.sqrt (1 - x^2)) volume (-1) 1 := by
    apply intervalIntegral.intervalIntegrable_deriv_of_nonneg Real.continuous_arcsin.continuousOn
    · simpa using hd
    · intro x hx
      positivity
  have hi' := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mp hi
  rw [← ofReal_integral_eq_lintegral_ofReal hi'
    (Filter.Eventually.of_forall fun x => by positivity)]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
    integral_inverse_sqrt_semicircle]

/-- The curvature −1 area of an ideal triangle is π. -/
theorem modelIdealTriangle_area :
    (∫⁻ z in modelIdealTriangle, ENNReal.ofReal ((z.2^2)⁻¹)
      ∂(volume.prod volume)) = ENNReal.ofReal Real.pi := by
  rw [← lintegral_indicator measurableSet_modelIdealTriangle]
  rw [lintegral_prod _ (by
    exact (Measurable.indicator (by fun_prop) measurableSet_modelIdealTriangle).aemeasurable)]
  have hsection (x : ℝ) :
      (∫⁻ y, modelIdealTriangle.indicator
        (fun z : ℝ × ℝ => ENNReal.ofReal ((z.2^2)⁻¹)) (x, y)) =
      (Ioo (-1 : ℝ) 1).indicator
        (fun x => ∫⁻ y in Ioi (Real.sqrt (1 - x^2)), ENNReal.ofReal ((y^2)⁻¹)) x := by
    by_cases hx : x ∈ Ioo (-1 : ℝ) 1
    · rw [indicator_of_mem hx, ← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro y
      simp only [modelIdealTriangle, indicator, mem_ofPred_eq, mem_Ioo, mem_Ioi,
        hx.1, hx.2, true_and]
    · have hx' : ¬ (-1 < x ∧ x < 1) := hx
      simp [modelIdealTriangle, hx', indicator]
  simp_rw [hsection]
  rw [lintegral_indicator measurableSet_Ioo]
  calc
    _ = ∫⁻ x in Ioo (-1 : ℝ) 1, ENNReal.ofReal (1 / Real.sqrt (1 - x^2)) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro x hx
      have hs : 0 < 1 - x^2 := by
        nlinarith [mul_pos (sub_pos.mpr hx.2) (by linarith [hx.1] : 0 < 1 + x)]
      simpa only [one_div] using lintegral_upper_halfPlane_vertical (Real.sqrt_pos.mpr hs)
    _ = ENNReal.ofReal Real.pi := lintegral_inverse_sqrt_semicircle

/-- The same model triangle in Mathlib's upper half-plane. -/
def upperHalfPlaneIdealTriangle : Set UpperHalfPlane :=
  {z | (z.re, z.im) ∈ modelIdealTriangle}

theorem complex_modelIdealTriangle_area :
    (∫⁻ z : ℂ in Complex.measurableEquivRealProd ⁻¹' modelIdealTriangle,
      ENNReal.ofReal ((z.im^2)⁻¹)) = ENNReal.ofReal Real.pi := by
  rw [← modelIdealTriangle_area]
  exact Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun z : ℝ × ℝ => ENNReal.ofReal ((z.2^2)⁻¹)) modelIdealTriangle

/-- The computed area agrees with Mathlib's invariant hyperbolic measure. -/
theorem upperHalfPlaneIdealTriangle_volume :
    volume upperHalfPlaneIdealTriangle = ENNReal.ofReal Real.pi := by
  have himage : UpperHalfPlane.coe '' upperHalfPlaneIdealTriangle =
      Complex.measurableEquivRealProd ⁻¹' modelIdealTriangle := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      have hpos : 0 < z.im := (Real.sqrt_nonneg _).trans_lt hz.2
      exact ⟨⟨z, hpos⟩, hz, rfl⟩
  rw [UpperHalfPlane.volume_eq_lintegral, himage]
  convert complex_modelIdealTriangle_area using 1
  apply lintegral_congr
  intro z
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp [sq_abs, inv_pow]

/-- Every Möbius image of the model triangle has the same hyperbolic area. -/
theorem upperHalfPlaneIdealTriangle_smul_volume (g : GL (Fin 2) ℝ) :
    volume (g • upperHalfPlaneIdealTriangle) = ENNReal.ofReal Real.pi := by
  rw [measure_smul, upperHalfPlaneIdealTriangle_volume]

theorem measurableSet_upperHalfPlaneIdealTriangle :
    MeasurableSet upperHalfPlaneIdealTriangle :=
  measurableSet_modelIdealTriangle.preimage (by fun_prop)

/-- Finite additivity for an ideal-triangle decomposition, allowing a null
exceptional boundary. Existence of the decomposition is a separate geometric
obligation; it is not supplied by this theorem. -/
theorem volume_of_idealTriangle_partition {ι : Type*} [Fintype ι]
    (g : ι → GL (Fin 2) ℝ) {s : Set UpperHalfPlane}
    (hdis : Pairwise fun i j =>
      Disjoint (g i • upperHalfPlaneIdealTriangle) (g j • upperHalfPlaneIdealTriangle))
    (hcover : s =ᵐ[volume] ⋃ i, g i • upperHalfPlaneIdealTriangle) :
    volume s = (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal Real.pi := by
  rw [measure_congr hcover, measure_iUnion hdis
    (fun i => measurableSet_upperHalfPlaneIdealTriangle.const_smul (g i))]
  simp [upperHalfPlaneIdealTriangle_volume, tsum_fintype, nsmul_eq_mul]

end AreaDeficit
