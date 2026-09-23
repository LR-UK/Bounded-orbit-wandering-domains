import EremenkosConjecture.ContinuumStage
import FunctionTheory.Conformal.StripInverseUniformity
import ComplexApproximation.Topology.ConformalArakelian
import TauCeti.Analysis.Complex.Conformal.LocalDegree

open Set Metric Filter Function Asymptotics
open scoped Topology

namespace EremenkosConjecture

/-- The actual strip-map estimates supply every local-chart field used by
the continuum induction, on a closed inset with bounded left truncations. -/
theorem exists_localIterateChart_of_strip_asymptotic
    {φ : ℂ → ℂ} {U P : Set ℂ} {L M R : ℝ} {c : ℂ}
    (hU : IsOpen U) (hUc : IsConnected U)
    (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U)
    (hP : IsClosed P) (hPU : P ⊆ U)
    (hleft : ∀ z ∈ P, L ≤ z.re) (him : ∀ z ∈ P, |z.im| ≤ M)
    (htail : ∀ z : ℂ, R < z.re → |z.im| ≤ M → z ∈ U)
    (hOd : (fun z => deriv φ z - 1) =O[comap Complex.re atTop ⊓ 𝓟 U]
      (fun z => Real.exp (-z.re)))
    (hOv : (fun z => φ z - (z + c)) =O[comap Complex.re atTop ⊓ 𝓟 U]
      (fun z => Real.exp (-z.re))) :
    ∃ D : LocalIterateChart φ 1 P, D.chart.source = U := by
  obtain ⟨e, heS, _, he, hei⟩ := exists_conformal_chart_of_injOn hU hφ hinj
    (fun z hz => TauCeti.deriv_ne_zero_of_injOn hφ hU hinj hz)
  have hre : Tendsto Complex.re (comap Complex.re atTop ⊓ 𝓟 U) atTop :=
    tendsto_comap.mono_left inf_le_left
  have hdecay : Tendsto (fun z : ℂ => Real.exp (-z.re))
      (comap Complex.re atTop ⊓ 𝓟 U) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hre)
  have hd : Tendsto (fun z => deriv φ z - 1)
      (comap Complex.re atTop ⊓ 𝓟 U) (𝓝 0) := hOd.trans_tendsto hdecay
  have hv : Tendsto (fun z => φ z - z)
      (comap Complex.re atTop ⊓ 𝓟 U) (𝓝 c) := by
    apply tendsto_sub_nhds_zero_iff.mp
    simpa only [sub_add_eq_sub_sub] using hOv.trans_tendsto hdecay
  have hPe : P ⊆ e.source := by simpa only [heS] using hPU
  have hvP : Tendsto (fun z => e z - z)
      (comap Complex.re atTop ⊓ 𝓟 P) (𝓝 c) := by
    simpa only [he] using hv.mono_left (inf_le_inf_left _ (Filter.principal_mono.mpr hPU))
  have hfwd : UniformContinuousOn e P :=
    FunctionTheory.uniformContinuousOn_of_strip_translation_limit hP hleft him
      (e.continuousOn.mono hPe) hvP
  have hinvUC : UniformContinuousOn e.symm (e '' P) :=
    FunctionTheory.uniformContinuousOn_inverse_of_strip_translation_limit e hP hPe
      hleft him hvP
  have ht : ComplexApproximation.HasHomeomorphicTailOn e P :=
    (ComplexApproximation.hasHomeomorphicTailOn_of_strip_derivative_limit
      hP hU hφ hleft him htail hd).congr (fun z _ => he z)
  exact ⟨⟨e, by simpa only [iterate_one] using he, hPe,
    by simpa only [heS] using hUc, hei, hfwd, hinvUC, ht⟩, heS⟩

end EremenkosConjecture
