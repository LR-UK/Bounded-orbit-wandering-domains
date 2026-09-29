module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

public import EremenkoLyubichConstant.PolynomialGrowth
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Ray.Dynamics.Multiple

@[expose] public section

open Filter Metric Set Function
open scoped Topology

namespace FunctionTheory

/-- An injective holomorphic punctured-disk parametrisation staying outside the unit disk,
along which an entire function has a pole, forces that entire function to be a polynomial.
This is the analytic exclusion of finite-sheeted exterior tracts. -/
theorem isPolynomialFunction_of_punctured_disc_model
    {f φ : ℂ → ℂ} (hf : Differentiable ℂ f) {r : ℝ} (hr : 0 < r)
    (hφ : DifferentiableOn ℂ φ (ball 0 r \ {0}))
    (hi : InjOn φ (ball 0 r \ {0}))
    (havoid : ∀ z ∈ ball 0 r \ {0}, 1 ≤ ‖φ z‖)
    (hm : MeromorphicAt (f ∘ φ) 0)
    (hescape : Tendsto (fun z ↦ ‖f (φ z)‖) (𝓝[≠] 0) atTop) :
    IsPolynomialFunction f := by
  classical
  let ψ : ℂ → ℂ := fun z ↦ (φ z)⁻¹
  have hne (z : ℂ) (hz : z ∈ ball 0 r \ {0}) : φ z ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (havoid z hz))
  have hψ : DifferentiableOn ℂ ψ (ball 0 r \ {0}) := hφ.inv hne
  have hb : BddAbove (norm ∘ ψ '' (ball 0 r \ {0})) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change ‖(φ z)⁻¹‖ ≤ 1
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ (havoid z hz)
  let g : ℂ → ℂ := update ψ 0 (limUnder (𝓝[≠] 0) ψ)
  have hball : ball (0 : ℂ) r ∈ 𝓝 0 := ball_mem_nhds 0 hr
  have hg : DifferentiableOn ℂ g (ball 0 r) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove hball hψ hb
  have hga : AnalyticAt ℂ g 0 := hg.analyticAt hball
  have hge (z : ℂ) (hz : z ≠ 0) : g z = (φ z)⁻¹ := update_of_ne hz _ _
  have hψlim : Tendsto ψ (𝓝[≠] 0) (𝓝 (g 0)) := by
    have h := continuousAt_update_same.mp hga.continuousAt
    simpa only [g, update_self] using h
  have hg0 : g 0 = 0 := by
    by_contra hn
    have hφlim : Tendsto φ (𝓝[≠] 0) (𝓝 (g 0)⁻¹) := by
      simpa only [ψ, inv_inv] using hψlim.inv₀ hn
    have hflim := (hf.continuous.continuousAt.tendsto.comp hφlim).norm
    exact not_tendsto_atTop_of_tendsto_nhds hflim hescape
  have hgnz (z : ℂ) (hz : z ∈ ball 0 r) (hz0 : z ≠ 0) : g z ≠ 0 := by
    rw [hge z hz0]
    exact inv_ne_zero (hne z ⟨hz, hz0⟩)
  have hgi : InjOn g (ball 0 r) := by
    intro x hx y hy hxy
    by_cases hx0 : x = 0
    · subst x
      by_contra hy0
      exact hgnz y hy (Ne.symm hy0) (hxy.symm.trans hg0)
    · by_cases hy0 : y = 0
      · subst y
        exact False.elim (hgnz x hx hx0 (hxy.trans hg0))
      · apply hi ⟨hx, hx0⟩ ⟨hy, hy0⟩
        exact inv_injective (by simpa only [hge x hx0, hge y hy0] using hxy)
  have hgd : deriv g 0 ≠ 0 := hgi.deriv_ne_zero isOpen_ball (mem_ball_self hr) hga
  apply isPolynomialFunction_of_meromorphicAt_infinity hf
  have hcomp : MeromorphicAt ((fun z : ℂ ↦ f z⁻¹) ∘ g) 0 := hm.congr <| by
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [mem_compl_iff, mem_singleton_iff] at hz
    simp [Function.comp_apply, hge z hz]
  have h := (meromorphicAt_comp_iff_of_deriv_ne_zero hga hgd).mp hcomp
  rwa [hg0] at h

/-- A finite-degree punctured-disk model of an exterior tract forces polynomiality. -/
theorem isPolynomialFunction_of_finite_tract_model
    {f φ : ℂ → ℂ} (hf : Differentiable ℂ f) {r : ℝ} (hr : 0 < r)
    (hφ : DifferentiableOn ℂ φ (ball 0 r \ {0}))
    (hi : InjOn φ (ball 0 r \ {0}))
    (havoid : ∀ z ∈ ball 0 r \ {0}, 1 ≤ ‖φ z‖)
    {a : ℂ} (ha : a ≠ 0) {d : ℕ} (hd : 0 < d)
    (heq : ∀ z ∈ ball 0 r \ {0}, f (φ z) = a * (z⁻¹) ^ d) :
    IsPolynomialFunction f := by
  have hev : (f ∘ φ) =ᶠ[𝓝[≠] 0] fun z ↦ a * (z⁻¹) ^ d := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) hr), self_mem_nhdsWithin]
      with z hz hz0
    exact heq z ⟨hz, hz0⟩
  apply isPolynomialFunction_of_punctured_disc_model hf hr hφ hi havoid
  · exact ((MeromorphicAt.const a 0).mul ((MeromorphicAt.id 0).inv.pow d)).congr hev.symm
  · have h := (tendsto_pow_atTop hd.ne').comp
      (tendsto_norm_inv_nhdsNE_zero_atTop (α := ℂ))
    have h' := h.const_mul_atTop (norm_pos_iff.mpr ha)
    apply h'.congr'
    filter_upwards [hev] with z hz
    simpa only [Function.comp_apply, norm_mul, norm_pow] using congrArg norm hz.symm

/-- A transcendental entire function has no finite-degree exterior tract model. -/
theorem IsTranscendentalEntire.no_finite_tract_model
    {f φ : ℂ → ℂ} (hf : IsTranscendentalEntire f) {r : ℝ} (hr : 0 < r)
    (hφ : DifferentiableOn ℂ φ (ball 0 r \ {0}))
    (hi : InjOn φ (ball 0 r \ {0}))
    (havoid : ∀ z ∈ ball 0 r \ {0}, 1 ≤ ‖φ z‖)
    {a : ℂ} (ha : a ≠ 0) {d : ℕ} (hd : 0 < d)
    (heq : ∀ z ∈ ball 0 r \ {0}, f (φ z) = a * (z⁻¹) ^ d) : False :=
  hf.2 (isPolynomialFunction_of_finite_tract_model hf.1 hr hφ hi havoid ha hd heq)

/-- The finite-tract exclusion only needs an omitted disk, with arbitrary center and radius. -/
theorem isPolynomialFunction_of_finite_tract_model_omitting_ball
    {f φ : ℂ → ℂ} (hf : Differentiable ℂ f) {r : ℝ} (hr : 0 < r)
    (hφ : DifferentiableOn ℂ φ (ball 0 r \ {0}))
    (hi : InjOn φ (ball 0 r \ {0}))
    {b : ℂ} {ε : ℝ} (hε : 0 < ε)
    (havoid : ∀ z ∈ ball 0 r \ {0}, ε ≤ ‖φ z - b‖)
    {a : ℂ} (ha : a ≠ 0) {d : ℕ} (hd : 0 < d)
    (heq : ∀ z ∈ ball 0 r \ {0}, f (φ z) = a * (z⁻¹) ^ d) :
    IsPolynomialFunction f := by
  have hc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
  let F : ℂ → ℂ := fun z ↦ f ((ε : ℂ) * z + b)
  let Φ : ℂ → ℂ := fun z ↦ (φ z - b) / (ε : ℂ)
  have hn (z : ℂ) : (ε : ℂ) * Φ z + b = φ z := by dsimp [Φ]; field_simp; ring
  have hF : Differentiable ℂ F := hf.comp (by fun_prop)
  have hΦ : DifferentiableOn ℂ Φ (ball 0 r \ {0}) := (hφ.sub_const b).div_const _
  have hΦi : InjOn Φ (ball 0 r \ {0}) := by
    intro z hz w hw he
    apply hi hz hw
    simpa only [hn] using congrArg (fun t : ℂ ↦ (ε : ℂ) * t + b) he
  have hΦb (z : ℂ) (hz : z ∈ ball 0 r \ {0}) : 1 ≤ ‖Φ z‖ := by
    simp only [Φ, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    exact (le_div_iff₀ hε).mpr (by simpa using havoid z hz)
  apply isPolynomialFunction_of_affine_precomp (a := b) hc
  apply isPolynomialFunction_of_finite_tract_model hF hr hΦ hΦi hΦb ha hd
  intro z hz
  change f ((ε : ℂ) * Φ z + b) = _
  rw [hn]
  exact heq z hz

end FunctionTheory
