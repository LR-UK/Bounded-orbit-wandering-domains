import LocalIntegratedDeficit
import ExceptionalSets

open Set Metric MeasureTheory Filter Function
open scoped Topology ENNReal

namespace AreaDeficit.FinitePunctureMetricInput

/-- The local dynamical area bound, including removal of critical
values and their local backward orbits. No exceptional-set avoidance
is required of the configuration. -/
theorem local_dynamical_area_bound (G : FinitePunctureMetricInput)
    {f : ℂ → ℂ} {V K : Set ℂ} (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hf : AnalyticOnNhd ℂ f (closure V))
    (hn : ∀ x ∈ closure V, ¬EventuallyConst f (𝓝 x))
    (hK : IsCompact K) (hKV : K ⊆ V) {a b : ℂ} (hab : a ≠ b) :
    ∃ H : ℝ≥0∞, H ≠ ∞ ∧ ∀ P : Finset ℂ, a ∈ P → b ∈ P →
      (∀ w ∈ V, w ∈ P → f w ∈ P) →
      ∀ B W : Set ℂ, MeasurableSet B → MeasurableSet W → B ⊆ W → W ⊆ K →
      InjOn f W → f '' W ⊆ W \ B → (∀ w ∈ W, f w ∉ P) →
      G.area P B ≤ H := by
  classical
  have hEfin := finite_local_critical_values hVc hf hn
  let E := hEfin.toFinset
  have hE : ∀ w ∈ V, deriv f w = 0 → f w ∈ E :=
    fun w hw hd => hEfin.mem_toFinset.mpr ⟨w, ⟨subset_closure hw, hd⟩, rfl⟩
  obtain ⟨H, hH, hbound⟩ := G.local_cancellation_bound hV (hf.mono subset_closure)
    (fun x hx => hn x (subset_closure hx)) hK hKV hab E hE
  let S := localBackwardExceptionalSet f V (↑E : Set ℂ)
  have hSc : S.Countable := localBackwardExceptionalSet_countable subset_closure hVc hf hn
    E.finite_toSet.countable
  have hback : V ∩ f ⁻¹' S ⊆ S := backwardTree_union_backward_invariant f V (↑E)
  have hES : (↑E : Set ℂ) ⊆ S := fun x hx => mem_iUnion.mpr ⟨0, hx⟩
  refine ⟨H, hH, ?_⟩
  intro P ha hb hp B W hB hW hBW hWK hinj himage havoid
  have hnull : G.area P S = 0 := withDensity_absolutelyContinuous volume _ (hSc.measure_zero volume)
  rw [← measure_sdiff_null (s := B) hnull]
  apply hbound P ha hb hp (B \ S) (W \ S)
    (hB.diff hSc.measurableSet) (hW.diff hSc.measurableSet)
    (sdiff_subset_sdiff_left hBW) (sdiff_subset.trans hWK) (hinj.mono sdiff_subset)
  · rintro y ⟨x, hx, rfl⟩
    have hy := himage (mem_image_of_mem f hx.1)
    exact ⟨⟨hy.1, fun hs => hx.2 (hback ⟨hKV (hWK hx.1), hs⟩)⟩,
      fun h => hy.2 h.1⟩
  · intro w hw hq
    rcases Finset.mem_union.mp hq with hwp | hwe
    · exact havoid w hw.1 hwp
    · exact hw.2 (hback ⟨hKV (hWK hw.1), hES hwe⟩)

end AreaDeficit.FinitePunctureMetricInput

#print axioms AreaDeficit.FinitePunctureMetricInput.local_dynamical_area_bound
