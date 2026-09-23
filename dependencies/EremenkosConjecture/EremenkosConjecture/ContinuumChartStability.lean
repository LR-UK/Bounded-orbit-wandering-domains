import EremenkosConjecture.ContinuumStage
import TauCeti.Analysis.Complex.Conformal.LocalDegree

open Set Metric Function
open scoped NNReal

namespace EremenkosConjecture

/-- After a small approximation has been expressed as a bi-Lipschitz change
of image coordinates, all local-chart fields pass to a smaller connected
open neighbourhood. -/
theorem exists_localIterateChart_of_image_change
    {f F : ℂ → ℂ} {m n : ℕ} {A U P : Set ℂ}
    (D : LocalIterateChart f m A) (hF : DifferentiableOn ℂ (F^[n]) U)
    (hU : IsOpen U) (hUc : IsConnected U) (hUA : U ⊆ A) (hPU : P ⊆ U)
    (H : ℂ ≃ₜ ℂ) {L L' : ℝ≥0} (hL : LipschitzWith L H)
    (hL' : LipschitzWith L' H.symm)
    (heq : EqOn (F^[n]) (H ∘ D.chart) A) :
    Nonempty (LocalIterateChart F n P) := by
  have hPA : P ⊆ A := hPU.trans hUA
  have hFU : DifferentiableOn ℂ (F^[n]) U := hF
  have hinj : InjOn (F^[n]) U := by
    intro x hx y hy hxy
    apply D.chart.injOn (D.contains (hUA hx)) (D.contains (hUA hy))
    apply H.injective
    exact (heq (hUA hx)).symm.trans (hxy.trans (heq (hUA hy)))
  obtain ⟨e, heS, heT, he, hei⟩ := exists_conformal_chart_of_injOn hU hFU hinj
    (fun z hz => TauCeti.deriv_ne_zero_of_injOn hFU hU hinj hz)
  have hPe : P ⊆ e.source := by simpa only [heS] using hPU
  have heH : EqOn e (H ∘ D.chart) A := fun z hz => (he z).trans (heq hz)
  have hforward : UniformContinuousOn e P :=
    (hL.uniformContinuous.comp_uniformContinuousOn (D.forward_uniform.mono hPA)).congr
      (heH.mono hPA).symm
  have hmap : MapsTo H.symm (e '' P) (D.chart '' A) := by
    rintro _ ⟨z, hz, rfl⟩
    have heHz : e z = H (D.chart z) := heH (hPA hz)
    rw [heHz, H.symm_apply_apply]
    exact mem_image_of_mem D.chart (hPA hz)
  have hinveq : EqOn (D.chart.symm ∘ H.symm) e.symm (e '' P) := by
    rintro _ ⟨z, hz, rfl⟩
    have heHz : e z = H (D.chart z) := heH (hPA hz)
    rw [comp_apply, heHz, H.symm_apply_apply, D.chart.left_inv (D.contains (hPA hz)),
      ← heHz, e.left_inv (hPe hz)]
  have hinverse : UniformContinuousOn e.symm (e '' P) :=
    (D.inverse_uniform.comp hL'.uniformContinuous.uniformContinuousOn hmap).congr hinveq
  have htail : ComplexApproximation.HasHomeomorphicTailOn e P :=
    ((D.tail.mono hPA).homeomorph_comp H).congr (heH.mono hPA)
  exact ⟨⟨e, he, hPe, by simpa only [heS] using hUc, hei, hforward, hinverse, htail⟩⟩

end EremenkosConjecture
