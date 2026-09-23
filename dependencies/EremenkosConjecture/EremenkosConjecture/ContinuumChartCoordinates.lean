import EremenkosConjecture.ContinuumStage

open Set Function

namespace EremenkosConjecture

/-- A holomorphic change of source coordinates preserves the chart data on
the corresponding closed inset. The uniformity assumptions hold for all affine
coordinate changes used in the return construction. -/
theorem LocalIterateChart.precomp_homeomorph
    {f : ℂ → ℂ} {n : ℕ} {P : Set ℂ} (D : LocalIterateChart f n P)
    (T : ℂ ≃ₜ ℂ) (hT : UniformContinuous T) (hTi : UniformContinuous T.symm)
    (hTh : Differentiable ℂ T.symm) :
    ∃ E : LocalIterateChart ((f^[n]) ∘ T) 1 (T ⁻¹' P),
      E.chart.source = T ⁻¹' D.chart.source := by
  let e := T.transOpenPartialHomeomorph D.chart
  have hPe : T ⁻¹' P ⊆ e.source := fun z hz => D.contains hz
  have hS : e.source = T.symm '' D.chart.source := by
    ext z
    change T z ∈ D.chart.source ↔ z ∈ T.symm '' D.chart.source
    constructor
    · intro hz
      exact ⟨T z, hz, T.symm_apply_apply z⟩
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
  have himage : e '' (T ⁻¹' P) = D.chart '' P := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨T z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨T.symm z, ?_, ?_⟩
      · simpa using hz
      · change D.chart (T (T.symm z)) = D.chart z
        rw [T.apply_symm_apply]
  have hinv : UniformContinuousOn e.symm (e '' (T ⁻¹' P)) := by
    rw [himage]
    exact hTi.comp_uniformContinuousOn D.inverse_uniform
  have htail : ComplexApproximation.HasHomeomorphicTailOn e (T ⁻¹' P) := by
    obtain ⟨K, hK, H, heH⟩ := D.tail
    refine ⟨T.symm '' K, hK.image T.symm.continuous, T.trans H, ?_⟩
    intro z hz
    apply heH
    refine ⟨hz.1, ?_⟩
    intro hTK
    exact hz.2 ⟨T z, hTK, T.symm_apply_apply z⟩
  refine ⟨⟨e, ?_, hPe, ?_, ?_, ?_, hinv, htail⟩, rfl⟩
  · intro z
    exact D.agrees (T z)
  · rw [hS]
    exact D.connected_source.image _ T.symm.continuous.continuousOn
  · exact hTh.comp_differentiableOn D.inverse_holomorphic
  · exact D.forward_uniform.comp hT.uniformContinuousOn (fun _ hz => hz)

/-- A biholomorphic affine change of image coordinates preserves the chart
data without shrinking the source. -/
theorem LocalIterateChart.postcomp_homeomorph
    {f : ℂ → ℂ} {n : ℕ} {P : Set ℂ} (D : LocalIterateChart f n P)
    (H : ℂ ≃ₜ ℂ) (hH : UniformContinuous H) (hHi : UniformContinuous H.symm)
    (hHh : Differentiable ℂ H.symm) :
    ∃ E : LocalIterateChart (H ∘ (f^[n])) 1 P,
      E.chart.source = D.chart.source := by
  let e := D.chart.transHomeomorph H
  have hmap : MapsTo H.symm (e '' P) (D.chart '' P) := by
    rintro _ ⟨z, hz, rfl⟩
    change H.symm (H (D.chart z)) ∈ D.chart '' P
    rw [H.symm_apply_apply]
    exact mem_image_of_mem D.chart hz
  refine ⟨⟨e, ?_, D.contains, D.connected_source, ?_, ?_, ?_,
    D.tail.homeomorph_comp H⟩, rfl⟩
  · intro z
    change H (D.chart z) = H ((f^[n]) z)
    rw [D.agrees]
  · exact D.inverse_holomorphic.comp hHh.differentiableOn (fun _ hz => hz)
  · exact hH.comp_uniformContinuousOn D.forward_uniform
  · exact D.inverse_uniform.comp hHi.uniformContinuousOn hmap

end EremenkosConjecture
