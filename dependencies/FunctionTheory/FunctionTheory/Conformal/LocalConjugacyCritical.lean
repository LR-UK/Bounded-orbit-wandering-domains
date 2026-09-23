import FunctionTheory.Conformal.InversePerturbation
import Mathlib.Analysis.Calculus.Deriv.Comp

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- A local conformal change of source and target preserves critical points. -/
theorem deriv_eq_zero_iff_of_local_conjugacy
    {f g α β : ℂ → ℂ} {a : ℂ}
    (hf : DifferentiableAt ℂ f a) (hg : DifferentiableAt ℂ g (α a))
    (hα : DifferentiableAt ℂ α a) (hβ : DifferentiableAt ℂ β (f a))
    (hαd : deriv α a ≠ 0) (hβd : deriv β (f a) ≠ 0)
    (heq : (fun z => g (α z)) =ᶠ[𝓝 a] (fun z => β (f z))) :
    deriv g (α a) = 0 ↔ deriv f a = 0 := by
  have HL := hg.hasDerivAt.comp a hα.hasDerivAt
  have HR := hβ.hasDerivAt.comp a hf.hasDerivAt
  have H : deriv g (α a) * deriv α a = deriv β (f a) * deriv f a :=
    HL.unique (HR.congr_of_eventuallyEq heq)
  constructor
  · intro hz
    rw [hz, zero_mul] at H
    exact (mul_eq_zero.mp H.symm).resolve_left hβd
  · intro hz
    rw [hz, mul_zero] at H
    exact (mul_eq_zero.mp H).resolve_right hαd

/-- Local nonconstancy transports through a neighbourhood conjugacy.
Only continuity of the source change is needed for this implication. -/
theorem locally_nonconstant_of_local_conjugacy
    {f g α β : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hα : ContinuousAt α a)
    (hβ : AnalyticAt ℂ β (f a)) (hβd : deriv β (f a) ≠ 0)
    (hnc : ¬ ∀ᶠ z in 𝓝 a, f z = f a)
    (heq : (fun z => g (α z)) =ᶠ[𝓝 a] (fun z => β (f z))) :
    ¬ ∀ᶠ z in 𝓝 (α a), g z = g (α a) := by
  intro hgconst
  have hbase : g (α a) = β (f a) := heq.eq_of_nhds
  have Hconst : ∀ᶠ z in 𝓝 a, β (f z) = β (f a) := by
    filter_upwards [hα.eventually hgconst, heq] with z hz hEqz
    exact hEqz.symm.trans (hz.trans hbase)
  have Horder : analyticOrderAt (fun z => β (f z) - β (f a)) a = ⊤ :=
    analyticOrderAt_eq_top.mpr (Hconst.mono (fun z hz => sub_eq_zero.mpr hz))
  rw [analyticOrderAt_centered_postcomp_of_deriv_ne_zero hf hβ hβd] at Horder
  exact hnc ((analyticOrderAt_eq_top.mp Horder).mono (fun z hz => sub_eq_zero.mp hz))

/-- If marked critical points are fixed by the source coordinates, critical
control on the original compact set becomes control by the same marked set
on its image. The conjugacy must hold on a neighbourhood of every point. -/
theorem critical_control_on_image_of_local_conjugacy
    {X C : Set ℂ} {f g α β : ℂ → ℂ}
    (hf : ∀ a ∈ X, DifferentiableAt ℂ f a)
    (hg : ∀ a ∈ X, DifferentiableAt ℂ g (α a))
    (hα : ∀ a ∈ X, DifferentiableAt ℂ α a)
    (hβ : ∀ a ∈ X, DifferentiableAt ℂ β (f a))
    (hαd : ∀ a ∈ X, deriv α a ≠ 0)
    (hβd : ∀ a ∈ X, deriv β (f a) ≠ 0)
    (heq : ∀ a ∈ X, (fun z => g (α z)) =ᶠ[𝓝 a] (fun z => β (f z)))
    (hcritical : ∀ a ∈ X, deriv f a = 0 → a ∈ C)
    (hfixed : ∀ a ∈ C, α a = a) :
    ∀ z ∈ α '' X, deriv g z = 0 → z ∈ C := by
  rintro z ⟨a, ha, rfl⟩ hz
  have hfa := (deriv_eq_zero_iff_of_local_conjugacy
    (hf a ha) (hg a ha) (hα a ha) (hβ a ha) (hαd a ha) (hβd a ha) (heq a ha)).mp hz
  have haC := hcritical a ha hfa
  rwa [hfixed a haC]

end FunctionTheory
