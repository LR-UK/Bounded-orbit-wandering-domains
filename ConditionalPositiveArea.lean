import LocalIntegratedDeficit
import LocalPunctureSequence
import PunctureDensityLimits
import ExceptionalSets

open Set Metric MeasureTheory Filter Function
open scoped Topology ENNReal

namespace AreaDeficit.FinitePunctureMetricInput

/-- Conditional local dynamical theorem for measurable wandering sets.
All metric limits, area comparisons, punctures, and exceptional sets
are constructed. The only geometric parameter is classical finite-
puncture metric data, with curvature −1. -/
theorem null_local_wandering_set_with_anchors (G : FinitePunctureMetricInput)
    {f : ℂ → ℂ} {V K : Set ℂ} (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hf : AnalyticOnNhd ℂ f (closure V))
    (hn : ∀ x ∈ closure V, ¬EventuallyConst f (𝓝 x))
    (hK : IsCompact K) (hKV : K ⊆ V)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∉ V) (hb : b ∉ V)
    {B : Set ℂ} (hB : MeasurableSet B)
    (hBT : B ⊆ trappedSet f V \ interior (trappedSet f V))
    (hwand : HasDisjointForwardImages f B)
    (hinj : InjOn f (forwardOrbit f B)) (hBK : forwardOrbit f B ⊆ K) :
    volume B = 0 := by
  classical
  have hfV := hf.mono (subset_closure : V ⊆ closure V)
  have hnV : ∀ x ∈ V, ¬EventuallyConst f (𝓝 x) := fun x hx => hn x (subset_closure hx)
  obtain ⟨P, hP, hanchors, hforward, havoid, hbarrier, _, _⟩ :=
    exists_local_puncture_sequence hV subset_closure hVc hf hn ha hb
  have hEfin := finite_local_critical_values hVc hf hn
  let E := hEfin.toFinset
  have hE : ∀ w ∈ V, deriv f w = 0 → f w ∈ E := by
    intro w hw hd
    exact hEfin.mem_toFinset.mpr ⟨w, ⟨subset_closure hw, hd⟩, rfl⟩
  obtain ⟨H, hH, hbound⟩ := G.local_cancellation_bound hV hfV hnV hK hKV hab E hE
  let S := localBackwardExceptionalSet f V (↑E : Set ℂ)
  have hSc : S.Countable :=
    localBackwardExceptionalSet_countable subset_closure hVc hf hn E.finite_toSet.countable
  let B' := B \ S
  have hB' : MeasurableSet B' := hB.diff hSc.measurableSet
  have hsub : B' ⊆ B := sdiff_subset
  have hWsub : forwardOrbit f B' ⊆ forwardOrbit f B := by
    intro x hx
    obtain ⟨n, y, hy, rfl⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n, y, hsub hy, rfl⟩
  have hw' : HasDisjointForwardImages f B' := by
    intro n m hnm
    exact (hwand hnm).mono (image_mono hsub) (image_mono hsub)
  have hi' : InjOn f (forwardOrbit f B') := hinj.mono hWsub
  have hc' : ContinuousOn f (forwardOrbit f B') :=
    hfV.continuousOn.mono (hWsub.trans (hBK.trans hKV))
  have hiter : ∀ n, InjOn (f^[n]) B' := fun n =>
    (hi'.iterate (mapsTo_iff_image_subset.mpr (image_forwardOrbit_subset f B')) n).mono
      (subset_forwardOrbit f B')
  have hW : MeasurableSet (forwardOrbit f B') := measurable_forwardOrbit hB' hw' hiter hc'
  have hweights : ∀ n, Measurable (fun z =>
      ENNReal.ofReal ((G.density (P n) z)^2 / (2 * Real.pi))) := by
    intro n
    have hc : 2 ≤ (P n).card := Finset.one_lt_card.mpr
      ⟨a, (hanchors n).1, b, (hanchors n).2, hab⟩
    exact ((G.measurable_density hc).pow_const 2 |>.div_const _).ennreal_ofReal
  have hzero : volume B' = 0 := by
    apply measure_zero_of_density_blowup hH (fun n => (hweights n).aemeasurable) ?_ ?_
    · filter_upwards [ae_restrict_mem hB'] with x hx
      have hxT := (hBT hx.1).1
      have hxA : x ∈ closure (⋃ n, (↑(P n) : Set ℂ)) :=
        ((Set.ext_iff.mp hbarrier x).mpr (hBT hx.1)).2
      have hd := G.density_tendsto_atTop hP hab (hanchors 0).1 (hanchors 0).2
        (fun n => havoid n x hxT) hxA
      apply ENNReal.tendsto_ofReal_atTop.comp
      simpa only [div_eq_mul_inv, Function.comp_apply] using
        ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hd).atTop_mul_const
          (by positivity : 0 < (2 * Real.pi)⁻¹)
    · intro n
      rw [← withDensity_apply _ hB']
      apply hbound (P n) (hanchors n).1 (hanchors n).2 (hforward n)
        B' (forwardOrbit f B') hB' hW (subset_forwardOrbit f B')
        (hWsub.trans hBK) hi' (image_forwardOrbit_eq_sdiff hw').subset
      intro w hw hwQ
      obtain ⟨k, x, hx, rfl⟩ := mem_iUnion.mp hw
      have hxT := (hBT hx.1).1
      have ht : f (f^[k] x) ∈ trappedSet f V :=
        trappedSet_forward f V ((trappedSet_forward f V).iterate k hxT)
      rcases Finset.mem_union.mp hwQ with hwp | hwe
      · exact havoid n _ ht hwp
      · have hav := trapped_orbit_avoids_of_not_localBackwardExceptionalSet hxT hx.2 (k + 1)
        apply hav
        simpa only [iterate_succ_apply', Finset.mem_coe] using hwe
  exact (measure_sdiff_null (hSc.measure_zero volume)).symm.trans hzero

/-- The two auxiliary anchors always exist outside a relatively compact
working domain, so they are not hypotheses of the final theorem. -/
theorem null_local_wandering_set (G : FinitePunctureMetricInput)
    {f : ℂ → ℂ} {V K : Set ℂ} (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hf : AnalyticOnNhd ℂ f (closure V))
    (hn : ∀ x ∈ closure V, ¬EventuallyConst f (𝓝 x))
    (hK : IsCompact K) (hKV : K ⊆ V)
    {B : Set ℂ} (hB : MeasurableSet B)
    (hBT : B ⊆ trappedSet f V \ interior (trappedSet f V))
    (hwand : HasDisjointForwardImages f B)
    (hinj : InjOn f (forwardOrbit f B)) (hBK : forwardOrbit f B ⊆ K) :
    volume B = 0 := by
  obtain ⟨R, hR, hVR⟩ := hVc.isBounded.exists_pos_norm_le
  have ha : ((R + 1 : ℝ) : ℂ) ∉ V := by
    intro hx
    have h := hVR _ (subset_closure hx)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h
    linarith
  have hb : ((R + 2 : ℝ) : ℂ) ∉ V := by
    intro hx
    have h := hVR _ (subset_closure hx)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h
    linarith
  apply G.null_local_wandering_set_with_anchors hV hVc hf hn hK hKV
    (a := ((R + 1 : ℝ) : ℂ)) (b := ((R + 2 : ℝ) : ℂ)) ?_ ha hb
    hB hBT hwand hinj hBK
  intro he
  have h := Complex.ofReal_injective he
  linarith

end AreaDeficit.FinitePunctureMetricInput

#print axioms AreaDeficit.FinitePunctureMetricInput.null_local_wandering_set_with_anchors
#print axioms AreaDeficit.FinitePunctureMetricInput.null_local_wandering_set
