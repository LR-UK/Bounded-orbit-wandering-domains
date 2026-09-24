/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

import EremenkoLyubichConstant.UniversalCover
import Ray.Dynamics.Multiple

open Set Filter Function
open scoped Topology

namespace FunctionTheory

/-- A continuous lift through a locally univalent holomorphic map is holomorphic. -/
theorem differentiableAt_of_continuousAt_comp_eq
    {f F g : ℂ → ℂ} {z : ℂ}
    (hF : ContinuousAt F z) (hf : AnalyticAt ℂ f (F z))
    (hd : deriv f (F z) ≠ 0) (hg : DifferentiableAt ℂ g z)
    (heq : ∀ᶠ x in 𝓝 z, f (F x) = g x) : DifferentiableAt ℂ F z := by
  let h := hf.hasStrictDerivAt
  let L := h.localInverse f (deriv f (F z)) (F z) hd
  have hL : DifferentiableAt ℂ L (f (F z)) :=
    (h.to_localInverse hd).hasDerivAt.differentiableAt
  let e := (h.hasStrictFDerivAt_equiv hd).toOpenPartialHomeomorph f
  have hsource : ∀ᶠ x in 𝓝 z, F x ∈ e.source :=
    hF.eventually (e.open_source.mem_nhds
      (h.hasStrictFDerivAt_equiv hd).mem_toOpenPartialHomeomorph_source)
  have heqz := heq.self_of_nhds
  have hcomp : DifferentiableAt ℂ (L ∘ g) z := (heqz ▸ hL).comp z hg
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [heq, hsource] with x hx hs
  change F x = L (g x)
  rw [← hx]
  exact (e.left_inv hs).symm

/-- An analytic local homeomorphism has nonzero complex derivative. -/
theorem deriv_ne_zero_of_isLocalHomeomorphOn
    {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hl : IsLocalHomeomorphOn f U) (hz : z ∈ U) :
    deriv f z ≠ 0 := by
  obtain ⟨e, he, hfe⟩ := hl z hz
  have hinj : InjOn f e.source := by rw [hfe]; exact e.injOn
  exact hinj.deriv_ne_zero e.open_source he hf

/-- Continuous lifts of holomorphic maps through holomorphic coverings are holomorphic. -/
theorem differentiableOn_of_continuousOn_covering_lift
    {f F g : ℂ → ℂ} {U V : Set ℂ}
    (hf : Differentiable ℂ f) (hc : IsCoveringMapOn f U) (hV : IsOpen V)
    (hF : ContinuousOn F V) (hFm : MapsTo (f ∘ F) V U)
    (hg : DifferentiableOn ℂ g V) (heq : EqOn (f ∘ F) g V) :
    DifferentiableOn ℂ F V := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_of_continuousAt_comp_eq
    (hF.continuousAt (hV.mem_nhds hz)) (hf.analyticAt (F z))
    (deriv_ne_zero_of_isLocalHomeomorphOn (hf.analyticAt (F z)) hc.isLocalHomeomorphOn (hFm hz))
    (hg.differentiableAt (hV.mem_nhds hz))
  exact (hV.eventually_mem hz).mono fun x hx ↦ heq hx

end FunctionTheory
