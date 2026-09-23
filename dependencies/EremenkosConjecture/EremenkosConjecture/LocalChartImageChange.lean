import EremenkosConjecture.ContinuumChartStability

open Set Function
open scoped NNReal

namespace EremenkosConjecture

/-- Transport a chart through a bi-Lipschitz change of its image, with
holomorphicity on the specified open source. Uniform estimates are needed
only on the closed inset, not on the whole source. -/
theorem exists_localIterateChart_on_source_of_image_change
    {f F : ℂ → ℂ} {m n : ℕ} {A U P : Set ℂ}
    (D : LocalIterateChart f m A) (hF : DifferentiableOn ℂ (F^[n]) U)
    (hU : IsOpen U) (hUc : IsConnected U) (hUD : U ⊆ D.chart.source)
    (hPU : P ⊆ U) (hPA : P ⊆ A)
    (H : ℂ ≃ₜ ℂ) {L L' : ℝ≥0} (hL : LipschitzWith L H)
    (hL' : LipschitzWith L' H.symm)
    (heq : EqOn (F^[n]) (H ∘ D.chart) U) :
    ∃ E : LocalIterateChart F n P, E.chart.source = U := by
  have hinj : InjOn (F^[n]) U := by
    intro x hx y hy hxy
    apply D.chart.injOn (hUD hx) (hUD hy)
    apply H.injective
    exact (heq hx).symm.trans (hxy.trans (heq hy))
  obtain ⟨e, heS, _, he, hei⟩ := exists_conformal_chart_of_injOn hU hF hinj
    (fun z hz => TauCeti.deriv_ne_zero_of_injOn hF hU hinj hz)
  have hPe : P ⊆ e.source := by simpa only [heS] using hPU
  have heH : EqOn e (H ∘ D.chart) P := fun z hz => (he z).trans (heq (hPU hz))
  have hforward : UniformContinuousOn e P :=
    (hL.uniformContinuous.comp_uniformContinuousOn (D.forward_uniform.mono hPA)).congr heH.symm
  have hmap : MapsTo H.symm (e '' P) (D.chart '' A) := by
    rintro _ ⟨z, hz, rfl⟩
    have heHz : e z = H (D.chart z) := heH hz
    rw [heHz, H.symm_apply_apply]
    exact mem_image_of_mem D.chart (hPA hz)
  have hinveq : EqOn (D.chart.symm ∘ H.symm) e.symm (e '' P) := by
    rintro _ ⟨z, hz, rfl⟩
    have heHz : e z = H (D.chart z) := heH hz
    rw [comp_apply, heHz, H.symm_apply_apply, D.chart.left_inv (D.contains (hPA hz)),
      ← heHz, e.left_inv (hPe hz)]
  have hinverse : UniformContinuousOn e.symm (e '' P) :=
    (D.inverse_uniform.comp hL'.uniformContinuous.uniformContinuousOn hmap).congr hinveq
  have htail : ComplexApproximation.HasHomeomorphicTailOn e P :=
    ((D.tail.mono hPA).homeomorph_comp H).congr heH
  exact ⟨⟨e, he, hPe, by simpa only [heS] using hUc,
    hei, hforward, hinverse, htail⟩, heS⟩

end EremenkosConjecture
