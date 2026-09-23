/- Adaptation: reduced imports only; declarations/proofs preserved from 0a6497b0cc9ed39a6a705bf013449635894b56d0. -/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic
/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.NormalFamilies.Spherical
import NoWanderingDomains.Sphere.SphereHolomorphic
import NoWanderingDomains.Sphere.InversionIsometry

/-!
# The spherical derivative, Marty's criterion, and Zalcman's lemma

The *spherical derivative* of a sphere-valued map is the operator norm of
the real derivative of its composition with the stereographic embedding
`stereoEmbed : ℂ̂ → S² ⊂ ℝ³`. On the finite chart it is the classical
`2‖u′‖/(1 + ‖u‖²)`; it is invariant under post-composition with the
inversion (a rotation of the sphere) and scales under affine
reparameterization.

Three theorems are developed on top of it:

* **Marty's criterion** (the sufficient direction,
  `isNormal_of_sphericalDeriv_le`): a family with locally bounded
  spherical derivative is spherically Lipschitz on convex sets, hence
  normal by an Arzelà–Ascoli diagonal over a countable dense set — the
  target sphere being compact.
* **Sphere-valued Weierstrass convergence**
  (`sphereHolomorphicOn_of_tendstoLocallyUniformlyOn`): locally uniform
  limits of sphere-holomorphic maps are sphere-holomorphic, with
  convergence of spherical derivatives.
* **Zalcman's rescaling lemma** (`exists_zalcman_rescale`): at a point of
  non-normality there are members `F k`, centers `z k → z₀`, and scales
  `ρ k ↓ 0` whose rescalings converge locally uniformly on all of `ℂ` to a
  nonconstant sphere-holomorphic limit `g` with `g# (0) = 1` and `g# ≤ 1`.
-/

open OnePoint Polynomial Filter Topology Metric Function

namespace NoWanderingDomains

/-- The *spherical derivative* of a sphere-valued map at a point: the
operator norm of the real derivative of its stereographic reading. At
points where the reading is not differentiable the junk value is `0`. -/
noncomputable def sphericalDeriv (F : ℂ → ℂ̂) (z : ℂ) : ℝ :=
  ‖fderiv ℝ (fun w => stereoEmbed (F w)) z‖

/-- The stereographic reading of the coercion of a holomorphic function is
real-differentiable. -/
theorem differentiableAt_stereoEmbed_comp_coe {u : ℂ → ℂ} {z : ℂ}
    (hu : DifferentiableAt ℂ u z) :
    DifferentiableAt ℝ (fun w => stereoEmbed ((u w : ℂ̂))) z := by
  -- `u` is `ℝ`-differentiable: build the `ℝ`-linear FDeriv directly from the
  -- `ℂ`-derivative (bypassing the `restrictScalars` type-class issue).
  have hur : HasFDerivAt u
      ((deriv u z) • (ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ)) z := by
    rw [hasFDerivAt_iff_isLittleO]
    refine hu.hasDerivAt.isLittleO.congr_left fun y => ?_
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    ring
  -- the stereographic reading of the identity chart is real-differentiable
  have hS : ∀ a : ℂ, DifferentiableAt ℝ (fun b : ℂ => stereoEmbed (b : ℂ̂)) a := by
    intro a
    have hden : (1 : ℝ) + ‖a‖ ^ 2 ≠ 0 := by positivity
    have hsq : DifferentiableAt ℝ (fun b : ℂ => ‖b‖ ^ 2) a :=
      differentiableAt_id.norm_sq ℝ
    have hd : DifferentiableAt ℝ (fun b : ℂ => 1 + ‖b‖ ^ 2) a :=
      (differentiableAt_const 1).add hsq
    have hre : DifferentiableAt ℝ (fun b : ℂ => b.re) a := Complex.reCLM.differentiableAt
    have him : DifferentiableAt ℝ (fun b : ℂ => b.im) a := Complex.imCLM.differentiableAt
    have hinv : DifferentiableAt ℝ (fun b : ℂ => ((1 : ℝ) + ‖b‖ ^ 2)⁻¹) a :=
      hd.fun_inv hden
    have hc0 : DifferentiableAt ℝ (fun b : ℂ => 2 * b.re * (1 + ‖b‖ ^ 2)⁻¹) a :=
      (hre.const_mul 2).fun_mul hinv
    have hc1 : DifferentiableAt ℝ (fun b : ℂ => 2 * b.im * (1 + ‖b‖ ^ 2)⁻¹) a :=
      (him.const_mul 2).fun_mul hinv
    have hc2 : DifferentiableAt ℝ (fun b : ℂ => (‖b‖ ^ 2 - 1) * (1 + ‖b‖ ^ 2)⁻¹) a :=
      (hsq.fun_sub (differentiableAt_const 1)).fun_mul hinv
    have hV : DifferentiableAt ℝ
        (fun b : ℂ => ![2 * b.re / (1 + ‖b‖ ^ 2), 2 * b.im / (1 + ‖b‖ ^ 2),
          (‖b‖ ^ 2 - 1) / (1 + ‖b‖ ^ 2)]) a := by
      rw [differentiableAt_pi]
      intro i
      fin_cases i
      · simpa [div_eq_mul_inv] using hc0
      · simpa [div_eq_mul_inv] using hc1
      · simpa [div_eq_mul_inv] using hc2
    exact (((EuclideanSpace.equiv (Fin 3) ℝ).symm).differentiableAt).comp a hV
  exact (hS (u z)).comp z hur.differentiableAt

/-- **The chart formula for the spherical derivative.** If `F` agrees near
`z` with the coercion of a holomorphic function `u`, then
`F# (z) = 2‖u′(z)‖/(1 + ‖u z‖²)`. -/
theorem sphericalDeriv_eq_of_eventuallyEq_coe {F : ℂ → ℂ̂} {u : ℂ → ℂ}
    {z : ℂ} (h : ∀ᶠ w in nhds z, F w = ((u w : ℂ) : ℂ̂))
    (hu : DifferentiableAt ℂ u z) :
    sphericalDeriv F z = 2 * ‖deriv u z‖ / (1 + ‖u z‖ ^ 2) := by
  have hdiff : DifferentiableAt ℝ (fun w => stereoEmbed ((u w : ℂ̂))) z :=
    differentiableAt_stereoEmbed_comp_coe hu
  have hur : HasFDerivAt u
      ((deriv u z) • (ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ)) z := by
    rw [hasFDerivAt_iff_isLittleO]
    refine hu.hasDerivAt.isLittleO.congr_left fun y => ?_
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    ring
  have heq : (fun w => stereoEmbed (F w)) =ᶠ[nhds z] fun w => stereoEmbed ((u w : ℂ̂)) :=
    h.mono fun w hw => by simp only [hw]
  have hfd : fderiv ℝ (fun w => stereoEmbed (F w)) z
      = fderiv ℝ (fun w => stereoEmbed ((u w : ℂ̂))) z := heq.fderiv_eq
  -- the chordal-distance identity for the embedding
  have hchord : ∀ a b : ℂ, ‖stereoEmbed (a : ℂ̂) - stereoEmbed (b : ℂ̂)‖
      = 2 * ‖a - b‖ / (Real.sqrt (1 + ‖a‖ ^ 2) * Real.sqrt (1 + ‖b‖ ^ 2)) := by
    intro a b
    rw [← dist_eq_norm, dist_stereoEmbed_eq_sphericalDist]
    rfl
  -- the pointwise norm of the differential, via slopes of the chordal distance
  have key : ∀ v : ℂ, ‖fderiv ℝ (fun w => stereoEmbed ((u w : ℂ̂))) z v‖
      = 2 * ‖deriv u z‖ / (1 + ‖u z‖ ^ 2) * ‖v‖ := by
    intro v
    have h0 : z + (0 : ℝ) • v = z := by simp
    have hline : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
    have hg : HasDerivAt (fun t : ℝ => stereoEmbed ((u (z + t • v) : ℂ̂)))
        (fderiv ℝ (fun w => stereoEmbed ((u w : ℂ̂))) z v) 0 :=
      hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline h0.symm
    have hu' : HasDerivAt (fun t : ℝ => u (z + t • v)) (deriv u z * v) 0 := by
      have h' := hur.comp_hasDerivAt_of_eq 0 hline h0.symm
      simpa [Function.comp_def] using h'
    have h1 : Tendsto
        (fun t : ℝ => ‖slope (fun s : ℝ => stereoEmbed ((u (z + s • v) : ℂ̂))) 0 t‖)
        (𝓝[≠] 0) (𝓝 ‖fderiv ℝ (fun w => stereoEmbed ((u w : ℂ̂))) z v‖) :=
      (hasDerivAt_iff_tendsto_slope.mp hg).norm
    have h2 : Tendsto (fun t : ℝ => ‖slope (fun s : ℝ => u (z + s • v)) 0 t‖)
        (𝓝[≠] 0) (𝓝 ‖deriv u z * v‖) :=
      (hasDerivAt_iff_tendsto_slope.mp hu').norm
    -- the continuity factor
    have hUc : Tendsto (fun t : ℝ => u (z + t • v)) (𝓝 0) (𝓝 (u z)) := by
      have h1' := hu'.continuousAt.tendsto
      simpa using h1'
    have hsq2 : Tendsto (fun t : ℝ => Real.sqrt (1 + ‖u (z + t • v)‖ ^ 2)) (𝓝 0)
        (𝓝 (Real.sqrt (1 + ‖u z‖ ^ 2))) :=
      (Real.continuous_sqrt.tendsto _).comp ((hUc.norm.pow 2).const_add 1)
    have hcont : Tendsto (fun t : ℝ => 2 / (Real.sqrt (1 + ‖u (z + t • v)‖ ^ 2)
        * Real.sqrt (1 + ‖u z‖ ^ 2))) (𝓝[≠] 0) (𝓝 (2 / (1 + ‖u z‖ ^ 2))) := by
      have hne : Real.sqrt (1 + ‖u z‖ ^ 2) * Real.sqrt (1 + ‖u z‖ ^ 2) ≠ 0 := by
        positivity
      have hdiv := (tendsto_const_nhds (x := (2 : ℝ))).div (hsq2.mul_const _) hne
      rw [Real.mul_self_sqrt (by positivity)] at hdiv
      exact hdiv.mono_left nhdsWithin_le_nhds
    -- identify the slope of the composite with the conformal product
    have hev : (fun t : ℝ => ‖slope (fun s : ℝ => stereoEmbed ((u (z + s • v) : ℂ̂))) 0 t‖)
        =ᶠ[𝓝[≠] 0] fun t : ℝ => 2 / (Real.sqrt (1 + ‖u (z + t • v)‖ ^ 2)
          * Real.sqrt (1 + ‖u z‖ ^ 2)) * ‖slope (fun s : ℝ => u (z + s • v)) 0 t‖ := by
      filter_upwards with t
      simp only [slope_def_module, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs, h0]
      rw [hchord]
      ring
    have h3 : Tendsto
        (fun t : ℝ => ‖slope (fun s : ℝ => stereoEmbed ((u (z + s • v) : ℂ̂))) 0 t‖)
        (𝓝[≠] 0) (𝓝 (2 / (1 + ‖u z‖ ^ 2) * ‖deriv u z * v‖)) :=
      (hcont.mul h2).congr' hev.symm
    have huniq : ‖fderiv ℝ (fun w => stereoEmbed ((u w : ℂ̂))) z v‖
        = 2 / (1 + ‖u z‖ ^ 2) * ‖deriv u z * v‖ := tendsto_nhds_unique h1 h3
    rw [huniq, norm_mul]
    ring
  have hnn : (0 : ℝ) ≤ 2 * ‖deriv u z‖ / (1 + ‖u z‖ ^ 2) := by positivity
  unfold sphericalDeriv
  rw [hfd]
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ hnn fun v => (key v).le) ?_
  have hle : ‖fderiv ℝ (fun w => stereoEmbed ((u w : ℂ̂))) z 1‖
      ≤ ‖fderiv ℝ (fun w => stereoEmbed ((u w : ℂ̂))) z‖ * ‖(1 : ℂ)‖ :=
    ContinuousLinearMap.le_opNorm _ 1
  rw [key 1, norm_one, mul_one, mul_one] at hle
  exact hle

/-- The spherical derivative is invariant under post-composition with the
inversion: `z ↦ 1/z` acts on the embedded sphere as the linear isometry
`(x, y, t) ↦ (x, -y, -t)`. -/
theorem sphericalDeriv_inversionGL_smul (F : ℂ → ℂ̂) (z : ℂ) :
    sphericalDeriv (fun w => inversionGL • F w) z = sphericalDeriv F z := by
  classical
  let L : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    LinearIsometryEquiv.piLpCongrRight 2 (fun i =>
      if i = 0 then LinearIsometryEquiv.refl ℝ ℝ else LinearIsometryEquiv.neg ℝ)
  have hL : ∀ x y t : ℝ, L ((EuclideanSpace.equiv (Fin 3) ℝ).symm ![x, y, t])
      = (EuclideanSpace.equiv (Fin 3) ℝ).symm ![x, -y, -t] := by
    intro x y t; apply PiLp.ext; intro i; fin_cases i <;> rfl
  have sInf : stereoEmbed (∞ : ℂ̂)
      = (EuclideanSpace.equiv (Fin 3) ℝ).symm ![(0 : ℝ), 0, 1] := rfl
  have sCoe : ∀ w : ℂ, stereoEmbed ((w : ℂ) : ℂ̂) = (EuclideanSpace.equiv (Fin 3) ℝ).symm
      ![2 * w.re / (1 + ‖w‖ ^ 2), 2 * w.im / (1 + ‖w‖ ^ 2), (‖w‖ ^ 2 - 1) / (1 + ‖w‖ ^ 2)] :=
    fun _ => rfl
  have e00 : 2 * (0 : ℂ).re / (1 + ‖(0 : ℂ)‖ ^ 2) = (0 : ℝ) := by simp
  have keyI : stereoEmbed (inversionGL • (∞ : ℂ̂)) = L (stereoEmbed (∞ : ℂ̂)) := by
    rw [inversionGL_smul_infty, sCoe, sInf, hL, e00]
    have e1 : 2 * (0 : ℂ).im / (1 + ‖(0 : ℂ)‖ ^ 2) = -(0 : ℝ) := by simp
    have e2 : (‖(0 : ℂ)‖ ^ 2 - 1) / (1 + ‖(0 : ℂ)‖ ^ 2) = -(1 : ℝ) := by norm_num
    rw [e1, e2]
  have keyC : ∀ b : ℂ, stereoEmbed (inversionGL • (b : ℂ̂)) = L (stereoEmbed ((b : ℂ̂))) := by
    intro b
    by_cases hb : b = 0
    · subst hb
      rw [inversionGL_smul_coe, if_pos rfl, sInf, sCoe, hL, e00]
      have e1 : -(2 * (0 : ℂ).im / (1 + ‖(0 : ℂ)‖ ^ 2)) = (0 : ℝ) := by simp
      have e2 : -((‖(0 : ℂ)‖ ^ 2 - 1) / (1 + ‖(0 : ℂ)‖ ^ 2)) = (1 : ℝ) := by norm_num
      rw [e1, e2]
    · rw [inversionGL_smul_coe, if_neg hb, sCoe, sCoe, hL]
      have hn0 : Complex.normSq b ≠ 0 := (Complex.normSq_pos.mpr hb).ne'
      have h := Complex.normSq_nonneg b
      have hn1 : (1 : ℝ) + Complex.normSq b ≠ 0 := by intro hcon; linarith
      have hn2 : Complex.normSq b + 1 ≠ 0 := by intro hcon; linarith
      have e0 : 2 * (b⁻¹).re / (1 + ‖b⁻¹‖ ^ 2) = 2 * b.re / (1 + ‖b‖ ^ 2) := by
        rw [Complex.inv_re, Complex.sq_norm, Complex.sq_norm, Complex.normSq_inv]
        field_simp; ring
      have e1 : 2 * (b⁻¹).im / (1 + ‖b⁻¹‖ ^ 2) = -(2 * b.im / (1 + ‖b‖ ^ 2)) := by
        rw [Complex.inv_im, Complex.sq_norm, Complex.sq_norm, Complex.normSq_inv]
        field_simp; ring
      have e2 : (‖b⁻¹‖ ^ 2 - 1) / (1 + ‖b⁻¹‖ ^ 2) = -((‖b‖ ^ 2 - 1) / (1 + ‖b‖ ^ 2)) := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_inv]
        field_simp; ring
      rw [e0, e1, e2]
  have key : ∀ p : ℂ̂, stereoEmbed (inversionGL • p) = L (stereoEmbed p) := by
    intro p
    match p with
    | ∞ => exact keyI
    | OnePoint.some b => exact keyC b
  have hfun : (fun w => stereoEmbed (inversionGL • F w))
      = (⇑L ∘ fun w => stereoEmbed (F w)) := funext fun w => key (F w)
  have heq : ∀ T : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3),
      (L.toContinuousLinearEquiv :
          EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)).comp T
        = L.toLinearIsometry.toContinuousLinearMap.comp T := by
    intro T; ext x; rfl
  simp only [sphericalDeriv]
  rw [hfun, L.comp_fderiv, heq, LinearIsometry.norm_toContinuousLinearMap_comp]

/-- The spherical derivative under affine reparameterization. -/
theorem sphericalDeriv_comp_affine (F : ℂ → ℂ̂) (a ρ z : ℂ) :
    sphericalDeriv (fun w => F (a + ρ * w)) z
      = ‖ρ‖ * sphericalDeriv F (a + ρ * z) := by
  classical
  simp only [sphericalDeriv]
  by_cases hρ : ρ = 0
  · subst hρ
    simp only [zero_mul, add_zero, norm_zero]
    rw [fderiv_const_apply, norm_zero]
  · have hA : ∀ w : ℂ,
        HasFDerivAt (fun v : ℂ => a + ρ * v) (ρ • ContinuousLinearMap.id ℝ ℂ) w :=
      fun w => ((hasFDerivAt_id w).const_mul ρ).const_add a
    have happ : ∀ (T : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3)) (h : ℂ),
        (T.comp (ρ • ContinuousLinearMap.id ℝ ℂ)) h = T (ρ * h) := by intro T h; simp
    have hρn : (0 : ℝ) < ‖ρ‖ := norm_pos_iff.mpr hρ
    have hcn : ∀ T : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3),
        ‖T.comp (ρ • ContinuousLinearMap.id ℝ ℂ)‖ = ‖ρ‖ * ‖T‖ := by
      intro T
      refine le_antisymm
        (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_) ?_
      · rw [happ]
        calc ‖T (ρ * h)‖ ≤ ‖T‖ * ‖ρ * h‖ := T.le_opNorm _
          _ = ‖ρ‖ * ‖T‖ * ‖h‖ := by rw [norm_mul]; ring
      · have hb : ‖T‖ ≤ ‖T.comp (ρ • ContinuousLinearMap.id ℝ ℂ)‖ * ‖ρ‖⁻¹ := by
          refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
          have hh : T h = (T.comp (ρ • ContinuousLinearMap.id ℝ ℂ)) (ρ⁻¹ * h) := by
            rw [happ, ← mul_assoc, mul_inv_cancel₀ hρ, one_mul]
          rw [hh]
          calc ‖(T.comp (ρ • ContinuousLinearMap.id ℝ ℂ)) (ρ⁻¹ * h)‖
              ≤ ‖T.comp (ρ • ContinuousLinearMap.id ℝ ℂ)‖ * ‖ρ⁻¹ * h‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ = ‖T.comp (ρ • ContinuousLinearMap.id ℝ ℂ)‖ * ‖ρ‖⁻¹ * ‖h‖ := by
                rw [norm_mul, norm_inv]; ring
        calc ‖ρ‖ * ‖T‖
            ≤ ‖ρ‖ * (‖T.comp (ρ • ContinuousLinearMap.id ℝ ℂ)‖ * ‖ρ‖⁻¹) :=
              mul_le_mul_of_nonneg_left hb hρn.le
          _ = ‖T.comp (ρ • ContinuousLinearMap.id ℝ ℂ)‖ := by
              rw [mul_comm _ ‖ρ‖⁻¹, ← mul_assoc, mul_inv_cancel₀ hρn.ne', one_mul]
    by_cases hdiff : DifferentiableAt ℝ (fun w => stereoEmbed (F w)) (a + ρ * z)
    · have h0 : HasFDerivAt ((fun w => stereoEmbed (F w)) ∘ fun v : ℂ => a + ρ * v)
          ((fderiv ℝ (fun w => stereoEmbed (F w)) (a + ρ * z)).comp
            (ρ • ContinuousLinearMap.id ℝ ℂ)) z :=
        hdiff.hasFDerivAt.comp z (hA z)
      have h1 : HasFDerivAt (fun w => stereoEmbed (F (a + ρ * w)))
          ((fderiv ℝ (fun w => stereoEmbed (F w)) (a + ρ * z)).comp
            (ρ • ContinuousLinearMap.id ℝ ℂ)) z := h0
      rw [h1.fderiv, hcn]
    · have h2 : ¬ DifferentiableAt ℝ (fun w => stereoEmbed (F (a + ρ * w))) z := by
        intro hcon
        apply hdiff
        have hB : DifferentiableAt ℝ (fun v : ℂ => ρ⁻¹ * (v - a)) (a + ρ * z) :=
          (differentiableAt_id.sub_const a).const_mul ρ⁻¹
        have hpt : ρ⁻¹ * (a + ρ * z - a) = z := by
          rw [add_sub_cancel_left, ← mul_assoc, inv_mul_cancel₀ hρ, one_mul]
        have hcon' : DifferentiableAt ℝ (fun w => stereoEmbed (F (a + ρ * w)))
            (ρ⁻¹ * (a + ρ * z - a)) := by rw [hpt]; exact hcon
        have hcomp := DifferentiableAt.comp (𝕜 := ℝ) (a + ρ * z) hcon' hB
        have hGeq : ((fun w => stereoEmbed (F (a + ρ * w))) ∘ fun v : ℂ => ρ⁻¹ * (v - a))
            = fun w => stereoEmbed (F w) := by
          funext v
          simp only [Function.comp_apply]
          have harg : a + ρ * (ρ⁻¹ * (v - a)) = v := by
            rw [← mul_assoc, mul_inv_cancel₀ hρ, one_mul]; ring
          rw [harg]
        rwa [hGeq] at hcomp
      rw [fderiv_zero_of_not_differentiableAt h2, fderiv_zero_of_not_differentiableAt hdiff]
      simp

/-- Sphere-holomorphy is preserved by affine reparameterization. -/
theorem SphereHolomorphicOn.comp_affine {F : ℂ → ℂ̂} {U : Set ℂ}
    (hF : SphereHolomorphicOn F U) (a ρ : ℂ) :
    SphereHolomorphicOn (fun w => F (a + ρ * w))
      ((fun w => a + ρ * w) ⁻¹' U) := by
  intro z hz
  obtain ⟨V, hVo, hzV, hVU, hd⟩ := hF (a + ρ * z) (Set.mem_preimage.mp hz)
  have hAc : Continuous (fun w : ℂ => a + ρ * w) :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hAd : DifferentiableOn ℂ (fun w : ℂ => a + ρ * w)
      ((fun w : ℂ => a + ρ * w) ⁻¹' V) :=
    ((differentiable_id.const_mul ρ).const_add a).differentiableOn
  refine ⟨(fun w : ℂ => a + ρ * w) ⁻¹' V, hVo.preimage hAc, Set.mem_preimage.mpr hzV,
    Set.preimage_mono hVU, ?_⟩
  rcases hd with ⟨hne, hdf⟩ | ⟨hne, hdf⟩
  · exact Or.inl ⟨fun w hw => hne _ (Set.mem_preimage.mp hw),
      hdf.comp hAd fun w hw => Set.mem_preimage.mp hw⟩
  · exact Or.inr ⟨fun w hw => hne _ (Set.mem_preimage.mp hw),
      hdf.comp hAd fun w hw => Set.mem_preimage.mp hw⟩

/-- The stereographic reading of a sphere-holomorphic map is
real-differentiable at every point of the domain. -/
theorem SphereHolomorphicOn.differentiableAt_stereoEmbed {F : ℂ → ℂ̂}
    {U : Set ℂ} (hF : SphereHolomorphicOn F U) {z : ℂ} (hz : z ∈ U) :
    DifferentiableAt ℝ (fun w => stereoEmbed (F w)) z := by
  obtain ⟨V, hVo, hzV, hVU, hcase⟩ := hF z hz
  rcases hcase with ⟨hne, hdiff⟩ | ⟨hne, hdiff⟩
  · -- Finite chart: `F` reads as the coercion of `chartFiniteMap ∘ F` near `z`.
    have hu : DifferentiableAt ℂ (fun w => chartFiniteMap (F w)) z :=
      hdiff.differentiableAt (hVo.mem_nhds hzV)
    have heq : (fun w => stereoEmbed (F w))
        =ᶠ[𝓝 z] fun w => stereoEmbed ((chartFiniteMap (F w) : ℂ) : ℂ̂) := by
      filter_upwards [hVo.mem_nhds hzV] with w hw
      cases hFw : F w with
      | infty => exact absurd hFw (hne w hw)
      | coe x => rfl
    exact (differentiableAt_stereoEmbed_comp_coe hu).congr_of_eventuallyEq heq
  · -- Infinity chart: `F w = inversionGL • ↑(chartInftyMap (F w))` near `z`, and the
    -- inversion acts on the embedded sphere as the rotation `(x, y, t) ↦ (x, -y, -t)`,
    -- which we write as `p ↦ (2 * p 0) • (1,0,0) - p`.
    have hv : DifferentiableAt ℂ (fun w => chartInftyMap (F w)) z :=
      hdiff.differentiableAt (hVo.mem_nhds hzV)
    have hg : DifferentiableAt ℝ
        (fun w => stereoEmbed ((chartInftyMap (F w) : ℂ) : ℂ̂)) z :=
      differentiableAt_stereoEmbed_comp_coe hv
    have hge : DifferentiableAt ℝ (fun w => EuclideanSpace.equiv (Fin 3) ℝ
        (stereoEmbed ((chartInftyMap (F w) : ℂ) : ℂ̂))) z :=
      (EuclideanSpace.equiv (Fin 3) ℝ).differentiableAt.comp z hg
    have hc0 : DifferentiableAt ℝ (fun w => EuclideanSpace.equiv (Fin 3) ℝ
        (stereoEmbed ((chartInftyMap (F w) : ℂ) : ℂ̂)) 0) z :=
      differentiableAt_pi.mp hge 0
    have hb : DifferentiableAt ℝ (fun w =>
        (2 * EuclideanSpace.equiv (Fin 3) ℝ
            (stereoEmbed ((chartInftyMap (F w) : ℂ) : ℂ̂)) 0) •
          (EuclideanSpace.equiv (Fin 3) ℝ).symm ![1, 0, 0]
        - stereoEmbed ((chartInftyMap (F w) : ℂ) : ℂ̂)) z :=
      ((hc0.const_mul 2).smul_const _).sub hg
    have hrot : ∀ a : ℂ, stereoEmbed (inversionGL • (a : ℂ̂))
        = (2 * EuclideanSpace.equiv (Fin 3) ℝ (stereoEmbed ((a : ℂ) : ℂ̂)) 0) •
            (EuclideanSpace.equiv (Fin 3) ℝ).symm ![1, 0, 0]
          - stereoEmbed ((a : ℂ) : ℂ̂) := by
      intro a
      have hsv : ∀ b : ℂ, EuclideanSpace.equiv (Fin 3) ℝ (stereoEmbed ((b : ℂ) : ℂ̂))
          = ![2 * b.re / (1 + ‖b‖ ^ 2), 2 * b.im / (1 + ‖b‖ ^ 2),
              (‖b‖ ^ 2 - 1) / (1 + ‖b‖ ^ 2)] := fun b => rfl
      apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
      rw [map_sub, _root_.map_smul, ContinuousLinearEquiv.apply_symm_apply, hsv]
      by_cases ha : a = 0
      · subst ha
        rw [inversionGL_smul_coe, if_pos rfl]
        have hsi : EuclideanSpace.equiv (Fin 3) ℝ (stereoEmbed (∞ : ℂ̂))
            = ![0, 0, 1] := rfl
        rw [hsi]
        funext i
        fin_cases i <;>
          norm_num [Pi.smul_apply, smul_eq_mul, Complex.zero_re, Complex.zero_im]
      · rw [inversionGL_smul_coe, if_neg ha, hsv]
        have hns : Complex.normSq a = ‖a‖ ^ 2 := (Complex.sq_norm a).symm
        have hna : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)
        have h1a : (1 : ℝ) + ‖a‖ ^ 2 ≠ 0 := by positivity
        have h1ai : (1 : ℝ) + (‖a‖ ^ 2)⁻¹ ≠ 0 := by positivity
        funext i
        fin_cases i <;> simp [Complex.inv_re, Complex.inv_im, hns] <;>
          field_simp <;> ring
    have heq : (fun w => stereoEmbed (F w)) =ᶠ[𝓝 z] fun w =>
        (2 * EuclideanSpace.equiv (Fin 3) ℝ
            (stereoEmbed ((chartInftyMap (F w) : ℂ) : ℂ̂)) 0) •
          (EuclideanSpace.equiv (Fin 3) ℝ).symm ![1, 0, 0]
        - stereoEmbed ((chartInftyMap (F w) : ℂ) : ℂ̂) := by
      filter_upwards [hVo.mem_nhds hzV] with w hw
      exact (congrArg stereoEmbed
        (inversionGL_smul_coe_chartInftyMap (hne w hw))).symm.trans
        (hrot (chartInftyMap (F w)))
    exact hb.congr_of_eventuallyEq heq

/-- The spherical derivative of a sphere-holomorphic map is continuous. -/
theorem SphereHolomorphicOn.continuousOn_sphericalDeriv {F : ℂ → ℂ̂}
    {U : Set ℂ} (hF : SphereHolomorphicOn F U) :
    ContinuousOn (sphericalDeriv F) U := by
  refine continuousOn_of_forall_continuousAt fun z hz => ?_
  -- The continuity argument in a single chart, applied to a map `G` that reads
  -- on `V` as the coercion of a holomorphic `u`.
  have key : ∀ (G : ℂ → ℂ̂) (u : ℂ → ℂ) (V : Set ℂ), IsOpen V → z ∈ V →
      (∀ w ∈ V, G w = ((u w : ℂ) : ℂ̂)) → DifferentiableOn ℂ u V →
      ContinuousAt (sphericalDeriv G) z := by
    intro G u V hVo hzV hGu hdiff
    have hfor : ∀ w ∈ V, sphericalDeriv G w = 2 * ‖deriv u w‖ / (1 + ‖u w‖ ^ 2) := by
      intro w hw
      refine sphericalDeriv_eq_of_eventuallyEq_coe ?_
        (hdiff.differentiableAt (hVo.mem_nhds hw))
      filter_upwards [hVo.mem_nhds hw] with w' hw'
      exact hGu w' hw'
    have hanc : AnalyticOnNhd ℂ u V := hdiff.analyticOnNhd hVo
    have hdc : ContinuousAt (deriv u) z :=
      hanc.deriv.continuousOn.continuousAt (hVo.mem_nhds hzV)
    have huc : ContinuousAt u z := hdiff.continuousOn.continuousAt (hVo.mem_nhds hzV)
    have hcont : ContinuousAt (fun w => 2 * ‖deriv u w‖ / (1 + ‖u w‖ ^ 2)) z := by
      have hden : (1 : ℝ) + ‖u z‖ ^ 2 ≠ 0 := by positivity
      exact (continuousAt_const.mul hdc.norm).div
        (continuousAt_const.add (huc.norm.pow 2)) hden
    refine hcont.congr ?_
    filter_upwards [hVo.mem_nhds hzV] with w hw
    exact (hfor w hw).symm
  obtain ⟨V, hVo, hzV, hVU, hcase⟩ := hF z hz
  rcases hcase with ⟨hne, hdiff⟩ | ⟨hne, hdiff⟩
  · -- Finite chart.
    refine key F (fun w => chartFiniteMap (F w)) V hVo hzV (fun w hw => ?_) hdiff
    have hcoe : F w = ((chartFiniteMap (F w) : ℂ) : ℂ̂) := by
      cases hFw : F w with
      | infty => exact absurd hFw (hne w hw)
      | coe x => rfl
    exact hcoe
  · -- Infinity chart: replace `F` by `inversionGL • F` using the invariance of the
    -- spherical derivative; the latter reads on `V` as the coercion of the
    -- infinity-chart reading of `F`.
    have hGv : ∀ w ∈ V, inversionGL • F w = ((chartInftyMap (F w) : ℂ) : ℂ̂) := by
      intro w hw
      cases hFw : F w with
      | infty => rw [inversionGL_smul_infty]; rfl
      | coe x =>
        have hx : x ≠ 0 := fun h => hne w hw (by rw [hFw, h])
        rw [inversionGL_smul_coe, if_neg hx]
        rfl
    have hflip : sphericalDeriv F = sphericalDeriv (fun w => inversionGL • F w) :=
      funext fun w => (sphericalDeriv_inversionGL_smul F w).symm
    rw [hflip]
    exact key (fun w => inversionGL • F w) (fun w => chartInftyMap (F w)) V hVo hzV
      hGv hdiff

/-- **The Marty–Lipschitz estimate**: a spherical-derivative bound on a
convex subset of the domain bounds the spherical distance between values
by `M` times the Euclidean distance. -/
theorem sphericalDist_le_of_sphericalDeriv_le {F : ℂ → ℂ̂} {U s : Set ℂ}
    (hF : SphereHolomorphicOn F U) (hsU : s ⊆ U)
    (hs : Convex ℝ s) {M : ℝ} (hM : ∀ z ∈ s, sphericalDeriv F z ≤ M)
    {x y : ℂ} (hx : x ∈ s) (hy : y ∈ s) :
    sphericalDist (F x) (F y) ≤ M * ‖x - y‖ := by
  have hd : ∀ w ∈ s, DifferentiableAt ℝ (fun w' => stereoEmbed (F w')) w :=
    fun w hw => SphereHolomorphicOn.differentiableAt_stereoEmbed hF (hsU hw)
  have hb : ∀ w ∈ s, ‖fderiv ℝ (fun w' => stereoEmbed (F w')) w‖ ≤ M :=
    fun w hw => hM w hw
  have key := hs.norm_image_sub_le_of_norm_fderiv_le hd hb hy hx
  calc sphericalDist (F x) (F y)
      = dist (stereoEmbed (F x)) (stereoEmbed (F y)) :=
        (dist_stereoEmbed_eq_sphericalDist (F x) (F y)).symm
    _ = ‖stereoEmbed (F x) - stereoEmbed (F y)‖ := dist_eq_norm _ _
    _ ≤ M * ‖x - y‖ := key

set_option maxHeartbeats 400000 in
-- The Arzelà–Ascoli diagonal over a countable dense set, plus several compactness
-- covers and an equi-Lipschitz upgrade, exceed the default heartbeat budget.
/-- **Marty's criterion** (sufficient direction): a family of
sphere-holomorphic maps with a uniform spherical-derivative bound is
normal — spherically equi-Lipschitz, hence normal by an Arzelà–Ascoli
diagonal over a countable dense set, the sphere being compact. -/
theorem isNormal_of_sphericalDeriv_le {𝓕 : Set (ℂ → ℂ̂)} {U : Set ℂ}
    (hU : IsOpen U) (hol : ∀ F ∈ 𝓕, SphereHolomorphicOn F U) {M : ℝ}
    (hM : ∀ F ∈ 𝓕, ∀ z ∈ U, sphericalDeriv F z ≤ M) :
    IsNormal 𝓕 U := by
  classical
  -- replace the bound by a nonnegative one
  set M' : ℝ := max M 0 with hM'def
  have hM'0 : (0 : ℝ) ≤ M' := le_max_right M 0
  have hM' : ∀ F ∈ 𝓕, ∀ z ∈ U, sphericalDeriv F z ≤ M' :=
    fun F hF z hz => (hM F hF z hz).trans (le_max_left M 0)
  -- the equi-Lipschitz estimate on balls inside `U` (spherical distance is `dist`)
  have key : ∀ G ∈ 𝓕, ∀ (z : ℂ) (δ : ℝ), ball z δ ⊆ U →
      ∀ x ∈ ball z δ, ∀ y ∈ ball z δ, dist (G x) (G y) ≤ M' * ‖x - y‖ := by
    intro G hG z δ hsub x hx y hy
    exact sphericalDist_le_of_sphericalDeriv_le (hol G hG) hsub (convex_ball z δ)
      (fun w hw => hM' G hG w (hsub hw)) hx hy
  intro seq
  have hch : ∀ n : ℕ, ∃ f₀ : ℂ → ℂ̂, f₀ ∈ 𝓕 ∧ f₀ = (seq n : ℂ → ℂ̂) :=
    fun n => ⟨(seq n : ℂ → ℂ̂), (seq n).2, rfl⟩
  choose F hFmem hFeq using hch
  -- a countable dense sequence in the plane
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq ℂ
  have hdense : ∀ x : ℂ, ∀ ρ : ℝ, 0 < ρ → ∃ j : ℕ, dist x (d j) < ρ :=
    fun x ρ hρ => Metric.denseRange_iff.mp hd x ρ hρ
  -- extraction kernel: pointwise convergence at `d j` for any reindexing (compact target)
  have step : ∀ (j : ℕ) (h : ℕ → ℕ), ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ y : ℂ̂, Tendsto (fun k => F (h (ψ k)) (d j)) atTop (nhds y) := by
    intro j h
    obtain ⟨y, -, ψ, hψ, hy⟩ := isCompact_univ.tendsto_subseq
      (x := fun n => F (h n) (d j)) fun n => Set.mem_univ _
    exact ⟨ψ, hψ, y, hy⟩
  choose ψ hψ Y hY using step
  -- nested subsequences: `σ (j+1) = σ j ∘ ψ (j+1) (σ j)`
  let σ : ℕ → ℕ → ℕ := fun j =>
    Nat.rec (motive := fun _ => ℕ → ℕ) (ψ 0 id) (fun i ih => ih ∘ ψ (i + 1) ih) j
  have σ_mono : ∀ j, StrictMono (σ j) := by
    intro j
    induction j with
    | zero => exact hψ 0 id
    | succ i ih => exact ih.comp (hψ (i + 1) (σ i))
  have σ_conv : ∀ j, ∃ y : ℂ̂, Tendsto (fun k => F (σ j k) (d j)) atTop (nhds y) := by
    intro j
    cases j with
    | zero => exact ⟨Y 0 id, hY 0 id⟩
    | succ i => exact ⟨Y (i + 1) (σ i), hY (i + 1) (σ i)⟩
  -- later stages refine earlier ones, with index growth
  have σ_refine : ∀ i m, ∃ ρ : ℕ → ℕ, (∀ k, k ≤ ρ k) ∧
      ∀ k, σ (i + m) k = σ i (ρ k) := by
    intro i m
    induction m with
    | zero => exact ⟨id, fun k => le_rfl, fun k => rfl⟩
    | succ m ih =>
      obtain ⟨ρ, hρ, heq⟩ := ih
      exact ⟨fun k => ρ (ψ (i + m + 1) (σ (i + m)) k),
        fun k => le_trans (hψ (i + m + 1) (σ (i + m))).le_apply (hρ _),
        fun k => heq (ψ (i + m + 1) (σ (i + m)) k)⟩
  -- the diagonal subsequence
  let dg : ℕ → ℕ := fun k => σ k k
  have dg_mono : StrictMono dg := by
    apply strictMono_nat_of_lt_succ
    intro k
    calc dg k = σ k k := rfl
      _ < σ k (k + 1) := σ_mono k (Nat.lt_succ_self k)
      _ ≤ σ k (ψ (k + 1) (σ k) (k + 1)) :=
          (σ_mono k).monotone (hψ (k + 1) (σ k)).le_apply
      _ = dg (k + 1) := rfl
  have dg_sub : ∀ j k, j ≤ k → ∃ m, k ≤ m ∧ dg k = σ j m := by
    intro j k hjk
    obtain ⟨ρ, hρ, heq⟩ := σ_refine j (k - j)
    have hk : j + (k - j) = k := Nat.add_sub_cancel' hjk
    have h2 := heq k
    rw [hk] at h2
    exact ⟨ρ k, hρ k, h2⟩
  -- the diagonal converges at every point of the dense sequence
  have dg_conv : ∀ j : ℕ, ∃ y : ℂ̂, Tendsto (fun k => F (dg k) (d j)) atTop (nhds y) := by
    intro j
    obtain ⟨y, hy⟩ := σ_conv j
    refine ⟨y, Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hy ε hε
    refine ⟨max j N, fun k hk => ?_⟩
    obtain ⟨m, hkm, hdm⟩ := dg_sub j k ((le_max_left j N).trans hk)
    rw [hdm]
    exact hN m (((le_max_right j N).trans hk).trans hkm)
  have dg_cauchy : ∀ j : ℕ, CauchySeq fun k => F (dg k) (d j) := by
    intro j
    obtain ⟨y, hy⟩ := dg_conv j
    exact hy.cauchySeq
  have hM1 : (0 : ℝ) < M' + 1 := by linarith
  -- the diagonal is pointwise Cauchy on all of `U` by the equi-Lipschitz estimate
  have ptwise : ∀ x ∈ U, CauchySeq fun k => F (dg k) x := by
    intro x hx
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hε3 : (0 : ℝ) < ε / (3 * (M' + 1)) := div_pos hε (by linarith)
    have harith : M' * (ε / (3 * (M' + 1))) ≤ ε / 3 := by
      calc M' * (ε / (3 * (M' + 1))) ≤ (M' + 1) * (ε / (3 * (M' + 1))) :=
            mul_le_mul_of_nonneg_right (by linarith) hε3.le
        _ = (M' + 1) * ε / ((M' + 1) * 3) := by ring
        _ = ε / 3 := mul_div_mul_left ε 3 hM1.ne'
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU x hx
    obtain ⟨j, hj⟩ := hdense x (min δ (ε / (3 * (M' + 1)))) (lt_min hδ hε3)
    have hdj : d j ∈ ball x δ := by
      rw [mem_ball, dist_comm]
      exact hj.trans_le (min_le_left _ _)
    have hnear : ∀ n : ℕ, dist (F n x) (F n (d j)) ≤ ε / 3 := by
      intro n
      have h1 := key (F n) (hFmem n) x δ hδU x (mem_ball_self hδ) (d j) hdj
      have h2 : ‖x - d j‖ ≤ ε / (3 * (M' + 1)) := by
        rw [← Complex.dist_eq]
        exact (hj.trans_le (min_le_right _ _)).le
      exact h1.trans ((mul_le_mul_of_nonneg_left h2 hM'0).trans harith)
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (dg_cauchy j) (ε / 3) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h3 := hN m hm n hn
    have h4 := hnear (dg m)
    have h5 := hnear (dg n)
    calc dist (F (dg m) x) (F (dg n) x)
        ≤ dist (F (dg m) x) (F (dg m) (d j)) + dist (F (dg m) (d j)) (F (dg n) (d j))
            + dist (F (dg n) (d j)) (F (dg n) x) := dist_triangle4 _ _ _ _
      _ < ε := by
          rw [dist_comm (F (dg n) (d j)) (F (dg n) x)]
          linarith
  -- the pointwise limit (the sphere is a complete — compact — metric space)
  have glex : ∀ x : ℂ, ∃ w : ℂ̂, x ∈ U → Tendsto (fun k => F (dg k) x) atTop (nhds w) := by
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete (ptwise x hx)
      exact ⟨w, fun _ => hw⟩
    · exact ⟨∞, fun h => absurd h hx⟩
  choose g hg using glex
  refine ⟨dg, dg_mono, g, ?_⟩
  have hseq_eq : (fun n => ((seq (dg n) : ℂ → ℂ̂))) = fun n => F (dg n) := by
    funext n
    exact (hFeq (dg n)).symm
  rw [hseq_eq, tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε3 : (0 : ℝ) < ε / (3 * (M' + 1)) := div_pos hε (by linarith)
  have harith : M' * (ε / (3 * (M' + 1))) ≤ ε / 3 := by
    calc M' * (ε / (3 * (M' + 1))) ≤ (M' + 1) * (ε / (3 * (M' + 1))) :=
          mul_le_mul_of_nonneg_right (by linarith) hε3.le
      _ = (M' + 1) * ε / ((M' + 1) * 3) := by ring
      _ = ε / 3 := mul_div_mul_left ε 3 hM1.ne'
  -- a Lipschitz ball inside `U` around each point of `K`, shrunk to scale `ε`
  have hKb : ∀ x ∈ K, ∃ δ : ℝ, 0 < δ ∧ ball x δ ⊆ U :=
    fun x hx => Metric.isOpen_iff.mp hU x (hKU hx)
  choose! δf hδf hδfU using hKb
  obtain ⟨T, hTK, hTcov⟩ := hK.elim_nhds_subcover
    (fun x => ball x (min (δf x / 2) (ε / (3 * (M' + 1)) / 2)))
    (fun x hx => ball_mem_nhds x (lt_min (half_pos (hδf x hx)) (half_pos hε3)))
  -- the small balls sit inside the Lipschitz balls
  have hssub : ∀ x ∈ K,
      ball x (min (δf x / 2) (ε / (3 * (M' + 1)) / 2)) ⊆ ball x (δf x) :=
    fun x hx => ball_subset_ball ((min_le_left _ _).trans (half_le_self (hδf x hx).le))
  -- a dense point selected in each cover ball
  have hsel : ∀ x ∈ T, ∃ j : ℕ, dist x (d j) < min (δf x / 2) (ε / (3 * (M' + 1)) / 2) :=
    fun x hx => hdense x _ (lt_min (half_pos (hδf x (hTK x hx))) (half_pos hε3))
  choose! jf hjf using hsel
  have hdjb : ∀ x ∈ T, d (jf x) ∈ ball x (min (δf x / 2) (ε / (3 * (M' + 1)) / 2)) := by
    intro x hx
    rw [mem_ball, dist_comm]
    exact hjf x hx
  -- the diagonal is eventually `ε/3`-close to the limit at the selected dense points
  have ev : ∀ᶠ k in atTop, ∀ x ∈ T, dist (g (d (jf x))) (F (dg k) (d (jf x))) < ε / 3 := by
    rw [Filter.eventually_all_finset]
    intro x hxT
    have hxK : x ∈ K := hTK x hxT
    have hdjU : d (jf x) ∈ U := hδfU x hxK (hssub x hxK (hdjb x hxT))
    have h1 := Metric.tendsto_nhds.mp (hg (d (jf x)) hdjU) (ε / 3) (by positivity)
    refine h1.mono fun k hk => ?_
    rwa [dist_comm]
  refine ev.mono fun k hk y hyK => ?_
  obtain ⟨x, hxT, hyb⟩ := Set.mem_iUnion₂.mp (hTcov hyK)
  have hxK : x ∈ K := hTK x hxT
  have hyU : y ∈ U := hδfU x hxK (hssub x hxK hyb)
  have hdjU : d (jf x) ∈ U := hδfU x hxK (hssub x hxK (hdjb x hxT))
  -- the distance from `y` to the selected dense point, at scale `ε`
  have hyd : ‖y - d (jf x)‖ ≤ ε / (3 * (M' + 1)) := by
    rw [← Complex.dist_eq]
    have h1 : dist y x < ε / (3 * (M' + 1)) / 2 :=
      (mem_ball.mp hyb).trans_le (min_le_right _ _)
    have h2 : dist x (d (jf x)) < ε / (3 * (M' + 1)) / 2 :=
      (hjf x hxT).trans_le (min_le_right _ _)
    calc dist y (d (jf x)) ≤ dist y x + dist x (d (jf x)) := dist_triangle _ _ _
      _ ≤ ε / (3 * (M' + 1)) := by linarith
  -- members are spherically Lipschitz between `y` and the dense point
  have hFlip : ∀ n : ℕ, dist (F n y) (F n (d (jf x))) ≤ ε / 3 := fun n =>
    (key (F n) (hFmem n) x (δf x) (hδfU x hxK) y (hssub x hxK hyb)
        (d (jf x)) (hssub x hxK (hdjb x hxT))).trans
      ((mul_le_mul_of_nonneg_left hyd hM'0).trans harith)
  -- so is the limit, by passing the estimate to the limit
  have hglip : dist (g y) (g (d (jf x))) ≤ ε / 3 :=
    le_of_tendsto ((hg y hyU).dist (hg (d (jf x)) hdjU))
      (Eventually.of_forall fun k' => hFlip (dg k'))
  have h2 := hk x hxT
  have h3 := hFlip (dg k)
  calc dist (g y) (F (dg k) y)
      ≤ dist (g y) (g (d (jf x))) + dist (g (d (jf x))) (F (dg k) (d (jf x)))
          + dist (F (dg k) (d (jf x))) (F (dg k) y) := dist_triangle4 _ _ _ _
    _ < ε := by
        rw [dist_comm (F (dg k) (d (jf x))) (F (dg k) y)]
        linarith

/-- At a point of non-normality, spherical derivatives blow up on every
neighborhood: otherwise a uniform bound on a small ball would make the
family normal there by Marty's criterion. -/
theorem exists_sphericalDeriv_gt_of_not_isNormalAt {𝓕 : Set (ℂ → ℂ̂)}
    {U : Set ℂ} (hU : IsOpen U) (hol : ∀ F ∈ 𝓕, SphereHolomorphicOn F U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hnot : ¬ IsNormalAt 𝓕 z₀) (M : ℝ) {r : ℝ}
    (hr : 0 < r) :
    ∃ F ∈ 𝓕, ∃ z : ℂ, ‖z - z₀‖ < r ∧ M < sphericalDeriv F z := by
  by_contra hcon
  push Not at hcon
  -- a uniform spherical-derivative bound on the ball makes the family normal there
  have hVo : IsOpen (ball z₀ r ∩ U) := isOpen_ball.inter hU
  have hzV : z₀ ∈ ball z₀ r ∩ U := ⟨mem_ball_self hr, hz₀⟩
  -- restrict sphere-holomorphy to the intersection
  have holV : ∀ F ∈ 𝓕, SphereHolomorphicOn F (ball z₀ r ∩ U) := by
    intro F hF z hz
    obtain ⟨W, hWo, hzW, hWU, hWalt⟩ := hol F hF z hz.2
    refine ⟨W ∩ (ball z₀ r ∩ U), hWo.inter hVo, ⟨hzW, hz⟩, Set.inter_subset_right, ?_⟩
    rcases hWalt with ⟨hne, hdiff⟩ | ⟨hne, hdiff⟩
    · exact Or.inl ⟨fun w hw => hne w hw.1, hdiff.mono Set.inter_subset_left⟩
    · exact Or.inr ⟨fun w hw => hne w hw.1, hdiff.mono Set.inter_subset_left⟩
  -- the spherical derivatives are bounded by `M` there
  have hMV : ∀ F ∈ 𝓕, ∀ z ∈ ball z₀ r ∩ U, sphericalDeriv F z ≤ M := by
    intro F hF z hz
    have hzr : ‖z - z₀‖ < r := by
      have h1 := hz.1
      rwa [mem_ball, Complex.dist_eq] at h1
    exact hcon F hF z hzr
  exact hnot ⟨ball z₀ r ∩ U, hVo.mem_nhds hzV,
    isNormal_of_sphericalDeriv_le hVo holV hMV⟩

/-- **Sphere-valued Weierstrass convergence**: a locally uniform limit of
sphere-holomorphic maps is sphere-holomorphic. Near a finite value of the
limit the chart readings converge locally uniformly and the planar
Weierstrass theorem applies; near `∞` the inversion (a spherical isometry)
reduces to the finite case. -/
theorem sphereHolomorphicOn_of_tendstoLocallyUniformlyOn {Fn : ℕ → ℂ → ℂ̂}
    {g : ℂ → ℂ̂} {U : Set ℂ} (hU : IsOpen U)
    (hol : ∀ n, SphereHolomorphicOn (Fn n) U)
    (hg : TendstoLocallyUniformlyOn Fn g atTop U) :
    SphereHolomorphicOn g U := by
  -- Finite-chart core, stated for an arbitrary family so it also applies after inversion.
  have key : ∀ (F : ℕ → ℂ → ℂ̂) (G : ℂ → ℂ̂), (∀ n, SphereHolomorphicOn (F n) U) →
      TendstoLocallyUniformlyOn F G atTop U → ∀ z₀ ∈ U, G z₀ ≠ ∞ →
      ∃ V, IsOpen V ∧ z₀ ∈ V ∧ V ⊆ U ∧ (∀ w ∈ V, G w ≠ ∞) ∧
        DifferentiableOn ℂ (fun w => chartFiniteMap (G w)) V := by
    intro F G holF hFG z₀ hz₀ hne
    have hGc : ContinuousOn G U :=
      hFG.continuousOn (Frequently.of_forall fun n => (holF n).continuousOn)
    obtain ⟨ε₀, hε₀, hd4⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ dist (G z₀) (∞ : ℂ̂) = 4 * ε₀ :=
      ⟨dist (G z₀) (∞ : ℂ̂) / 4, by linarith [dist_pos.mpr hne], by ring⟩
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp (hGc.continuousAt (hU.mem_nhds hz₀)) ε₀ hε₀
    obtain ⟨r₁, hr₁, hr₁U⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz₀)
    obtain ⟨r, hr, hrδ, hrU⟩ : ∃ r : ℝ, 0 < r ∧ r < δ ∧ closedBall z₀ r ⊆ U :=
      ⟨min r₁ (δ / 2), lt_min hr₁ (by linarith), lt_of_le_of_lt (min_le_right _ _) (by linarith),
        (closedBall_subset_closedBall (min_le_left _ _)).trans hr₁U⟩
    -- values of `G` on the closed ball stay spherically far from `∞`
    have hGfar : ∀ w ∈ closedBall z₀ r, 3 * ε₀ ≤ dist (G w) (∞ : ℂ̂) := by
      intro w hw
      have h2 := dist_triangle (G z₀) (G w) (∞ : ℂ̂)
      have h3 : dist (G z₀) (G w) < ε₀ := by
        rw [dist_comm]
        exact hδ' (lt_of_le_of_lt (mem_closedBall.mp hw) hrδ)
      linarith
    -- points spherically far from `∞` are finite with bounded chart reading
    have hbound : ∀ p : ℂ̂, 2 * ε₀ ≤ dist p (∞ : ℂ̂) →
        p ≠ ∞ ∧ ‖chartFiniteMap p‖ ≤ 2 / (2 * ε₀) := by
      intro p hp
      cases p with
      | infty =>
        rw [dist_self] at hp
        exact absurd hp (not_le.mpr (by linarith))
      | coe x =>
        refine ⟨OnePoint.coe_ne_infty x, ?_⟩
        have hx_eq : dist ((x : ℂ̂)) (∞ : ℂ̂) = 2 / Real.sqrt (1 + ‖x‖ ^ 2) := rfl
        rw [hx_eq] at hp
        have hs : 0 < Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
        have hxs : ‖x‖ ≤ Real.sqrt (1 + ‖x‖ ^ 2) :=
          calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
            _ ≤ Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg ‖x‖])
        have h2 : 2 * ε₀ * Real.sqrt (1 + ‖x‖ ^ 2) ≤ 2 := (le_div_iff₀ hs).mp hp
        have h3 : Real.sqrt (1 + ‖x‖ ^ 2) ≤ 2 / (2 * ε₀) := by
          rw [le_div_iff₀ (by positivity)]
          linarith [mul_comm (2 * ε₀) (Real.sqrt (1 + ‖x‖ ^ 2))]
        exact hxs.trans h3
    have hcoe : ∀ p : ℂ̂, p ≠ ∞ → ((chartFiniteMap p : ℂ) : ℂ̂) = p := by
      intro p hp
      cases p with
      | infty => exact absurd rfl hp
      | coe x => rfl
    have hunif : TendstoUniformlyOn F G atTop (closedBall z₀ r) :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hFG _ hrU (isCompact_closedBall z₀ r)
    -- eventually the members are close to `G`, hence also far from `∞`, on the ball
    have hFev : ∀ᶠ n in atTop, ∀ w ∈ closedBall z₀ r,
        dist (G w) (F n w) < ε₀ ∧ 2 * ε₀ ≤ dist (F n w) (∞ : ℂ̂) := by
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif ε₀ hε₀] with n hn w hw
      have h2 := hGfar w hw
      have h3 := dist_triangle (G w) (F n w) (∞ : ℂ̂)
      exact ⟨hn w hw, by linarith [hn w hw]⟩
    -- eventually the chart readings of the members are holomorphic on the open ball
    have hudiff : ∀ᶠ n in atTop,
        DifferentiableOn ℂ (fun w => chartFiniteMap (F n w)) (ball z₀ r) := by
      filter_upwards [hFev] with n hn
      refine SphereHolomorphicOn.differentiableOn_chartFiniteMap (fun w hw => ?_) (fun w hw => ?_)
      · obtain ⟨V, hVo, hwV, hVU, hcase⟩ := holF n w (hrU (ball_subset_closedBall hw))
        refine ⟨V ∩ ball z₀ r, hVo.inter isOpen_ball, ⟨hwV, hw⟩, Set.inter_subset_right, ?_⟩
        rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨fun x hx => h1 x hx.1, h2.mono Set.inter_subset_left⟩
        · exact Or.inr ⟨fun x hx => h1 x hx.1, h2.mono Set.inter_subset_left⟩
      · exact (hbound _ (hn w (ball_subset_closedBall hw)).2).1
    obtain ⟨C, hC0, hCdef⟩ : ∃ C : ℝ, 0 < C ∧ C = (1 + (2 / (2 * ε₀)) ^ 2) / 2 :=
      ⟨(1 + (2 / (2 * ε₀)) ^ 2) / 2, by positivity, rfl⟩
    have hC0' : C ≠ 0 := ne_of_gt hC0
    -- the chart readings converge uniformly on the closed ball
    have huTLU : TendstoUniformlyOn (fun n w => chartFiniteMap (F n w))
        (fun w => chartFiniteMap (G w)) atTop (closedBall z₀ r) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [hFev, Metric.tendstoUniformlyOn_iff.mp hunif (ε / C) (by positivity)]
        with n hn hn2 w hw
      obtain ⟨hFne, hFbd⟩ := hbound _ (hn w hw).2
      obtain ⟨hGne, hGbd⟩ := hbound _ (le_trans (by linarith) (hGfar w hw))
      have hnorm := norm_sub_le_sphericalDist_mul hGbd hFbd
      have hds : sphericalDist ((chartFiniteMap (G w) : ℂ) : ℂ̂)
          ((chartFiniteMap (F n w) : ℂ) : ℂ̂) = dist (G w) (F n w) := by
        rw [hcoe _ hGne, hcoe _ hFne]
        rfl
      rw [hds, ← hCdef] at hnorm
      calc dist (chartFiniteMap (G w)) (chartFiniteMap (F n w))
          = ‖chartFiniteMap (G w) - chartFiniteMap (F n w)‖ := dist_eq_norm _ _
        _ ≤ C * dist (G w) (F n w) := hnorm
        _ < C * (ε / C) := mul_lt_mul_of_pos_left (hn2 w hw) hC0
        _ = ε := by field_simp
    -- planar Weierstrass: the limit chart reading is holomorphic on the open ball
    have huGdiff : DifferentiableOn ℂ (fun w => chartFiniteMap (G w)) (ball z₀ r) :=
      (huTLU.tendstoLocallyUniformlyOn.mono ball_subset_closedBall).differentiableOn
        hudiff isOpen_ball
    refine ⟨ball z₀ r, isOpen_ball, mem_ball_self hr,
      ball_subset_closedBall.trans hrU, fun w hw => ?_, huGdiff⟩
    exact (hbound _ (le_trans (by linarith) (hGfar w (ball_subset_closedBall hw)))).1
  intro z₀ hz₀
  by_cases hzi : g z₀ = ∞
  · -- pass to the inversion: a spherical isometry exchanging `∞` and `0`
    have hol' : ∀ n, SphereHolomorphicOn (fun w => inversionGL • Fn n w) U := fun n =>
      (hol n).gl_smul inversionGL
    have hg' : TendstoLocallyUniformlyOn (fun n w => inversionGL • Fn n w)
        (fun w => inversionGL • g w) atTop U := by
      rw [Metric.tendstoLocallyUniformlyOn_iff] at hg ⊢
      intro ε hε x hx
      obtain ⟨t, ht, hev⟩ := hg ε hε x hx
      refine ⟨t, ht, hev.mono fun n hn y hy => ?_⟩
      exact lt_of_eq_of_lt (sphericalDist_inversionGL_smul (g y) (Fn n y)) (hn y hy)
    have hne : inversionGL • g z₀ ≠ ∞ := by
      rw [hzi, inversionGL_smul_infty]
      exact OnePoint.coe_ne_infty 0
    obtain ⟨V, hVo, hzV, hVU, hVne, hVdiff⟩ := key _ _ hol' hg' z₀ hz₀ hne
    have cf : ∀ x : ℂ, chartFiniteMap (x : ℂ̂) = x := fun _ => rfl
    have ci : ∀ x : ℂ, chartInftyMap (x : ℂ̂) = x⁻¹ := fun _ => rfl
    have cf0 : chartFiniteMap (∞ : ℂ̂) = 0 := rfl
    have ci0 : chartInftyMap (∞ : ℂ̂) = 0 := rfl
    -- the infinity-chart reading of `g` is the finite-chart reading of `inversionGL • g`
    have hkey : ∀ p : ℂ̂, chartInftyMap p = chartFiniteMap (inversionGL • p) := by
      intro p
      cases p with
      | infty => rw [ci0, inversionGL_smul_infty, cf]
      | coe x =>
        by_cases hx : x = 0
        · subst hx
          rw [inversionGL_smul_coe, if_pos rfl, ci, inv_zero, cf0]
        · rw [inversionGL_smul_coe, if_neg hx, ci, cf]
    refine ⟨V, hVo, hzV, hVU, Or.inr ⟨fun w hw hc => ?_,
      hVdiff.congr fun w _ => hkey (g w)⟩⟩
    have h1 : inversionGL • g w = ∞ := by rw [hc, inversionGL_smul_coe, if_pos rfl]
    exact hVne w hw h1
  · obtain ⟨V, hVo, hzV, hVU, hVne, hVdiff⟩ := key Fn g hol hg z₀ hz₀ hzi
    exact ⟨V, hVo, hzV, hVU, Or.inl ⟨hVne, hVdiff⟩⟩

-- Spherical derivatives converge pointwise under locally uniform convergence
-- of sphere-holomorphic maps.
set_option maxHeartbeats 400000 in -- chart-transfer machinery is long

/-- Spherical derivatives converge pointwise under locally uniform
convergence of sphere-holomorphic maps. -/
theorem tendsto_sphericalDeriv_of_tendstoLocallyUniformlyOn
    {Fn : ℕ → ℂ → ℂ̂} {g : ℂ → ℂ̂} {U : Set ℂ} (hU : IsOpen U)
    (hol : ∀ n, SphereHolomorphicOn (Fn n) U)
    (hg : TendstoLocallyUniformlyOn Fn g atTop U) {z : ℂ} (hz : z ∈ U) :
    Tendsto (fun n => sphericalDeriv (Fn n) z) atTop
      (nhds (sphericalDeriv g z)) := by
  -- Finite-chart core, stated for an arbitrary family so it also applies after inversion.
  have key : ∀ (F : ℕ → ℂ → ℂ̂) (G : ℂ → ℂ̂), (∀ n, SphereHolomorphicOn (F n) U) →
      TendstoLocallyUniformlyOn F G atTop U → G z ≠ ∞ →
      Tendsto (fun n => sphericalDeriv (F n) z) atTop (nhds (sphericalDeriv G z)) := by
    intro F G holF hFG hne
    have hGc : ContinuousOn G U :=
      hFG.continuousOn (Frequently.of_forall fun n => (holF n).continuousOn)
    obtain ⟨ε₀, hε₀, hd4⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ dist (G z) (∞ : ℂ̂) = 4 * ε₀ :=
      ⟨dist (G z) (∞ : ℂ̂) / 4, by linarith [dist_pos.mpr hne], by ring⟩
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp (hGc.continuousAt (hU.mem_nhds hz)) ε₀ hε₀
    obtain ⟨r₁, hr₁, hr₁U⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz)
    obtain ⟨r, hr, hrδ, hrU⟩ : ∃ r : ℝ, 0 < r ∧ r < δ ∧ closedBall z r ⊆ U :=
      ⟨min r₁ (δ / 2), lt_min hr₁ (by linarith), lt_of_le_of_lt (min_le_right _ _) (by linarith),
        (closedBall_subset_closedBall (min_le_left _ _)).trans hr₁U⟩
    have hGfar : ∀ w ∈ closedBall z r, 3 * ε₀ ≤ dist (G w) (∞ : ℂ̂) := by
      intro w hw
      have h2 := dist_triangle (G z) (G w) (∞ : ℂ̂)
      have h3 : dist (G z) (G w) < ε₀ := by
        rw [dist_comm]
        exact hδ' (lt_of_le_of_lt (mem_closedBall.mp hw) hrδ)
      linarith
    have hbound : ∀ p : ℂ̂, 2 * ε₀ ≤ dist p (∞ : ℂ̂) →
        p ≠ ∞ ∧ ‖chartFiniteMap p‖ ≤ 2 / (2 * ε₀) := by
      intro p hp
      cases p with
      | infty =>
        rw [dist_self] at hp
        exact absurd hp (not_le.mpr (by linarith))
      | coe x =>
        refine ⟨OnePoint.coe_ne_infty x, ?_⟩
        have hx_eq : dist ((x : ℂ̂)) (∞ : ℂ̂) = 2 / Real.sqrt (1 + ‖x‖ ^ 2) := rfl
        rw [hx_eq] at hp
        have hs : 0 < Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
        have hxs : ‖x‖ ≤ Real.sqrt (1 + ‖x‖ ^ 2) :=
          calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
            _ ≤ Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg ‖x‖])
        have h2 : 2 * ε₀ * Real.sqrt (1 + ‖x‖ ^ 2) ≤ 2 := (le_div_iff₀ hs).mp hp
        have h3 : Real.sqrt (1 + ‖x‖ ^ 2) ≤ 2 / (2 * ε₀) := by
          rw [le_div_iff₀ (by positivity)]
          linarith [mul_comm (2 * ε₀) (Real.sqrt (1 + ‖x‖ ^ 2))]
        exact hxs.trans h3
    have hcoe : ∀ p : ℂ̂, p ≠ ∞ → ((chartFiniteMap p : ℂ) : ℂ̂) = p := by
      intro p hp
      cases p with
      | infty => exact absurd rfl hp
      | coe x => rfl
    have hunif : TendstoUniformlyOn F G atTop (closedBall z r) :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hFG _ hrU (isCompact_closedBall z r)
    have hFev : ∀ᶠ n in atTop, ∀ w ∈ closedBall z r,
        dist (G w) (F n w) < ε₀ ∧ 2 * ε₀ ≤ dist (F n w) (∞ : ℂ̂) := by
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif ε₀ hε₀] with n hn w hw
      have h2 := hGfar w hw
      have h3 := dist_triangle (G w) (F n w) (∞ : ℂ̂)
      exact ⟨hn w hw, by linarith [hn w hw]⟩
    have hudiff : ∀ᶠ n in atTop,
        DifferentiableOn ℂ (fun w => chartFiniteMap (F n w)) (ball z r) := by
      filter_upwards [hFev] with n hn
      refine SphereHolomorphicOn.differentiableOn_chartFiniteMap (fun w hw => ?_) (fun w hw => ?_)
      · obtain ⟨V, hVo, hwV, hVU, hcase⟩ := holF n w (hrU (ball_subset_closedBall hw))
        refine ⟨V ∩ ball z r, hVo.inter isOpen_ball, ⟨hwV, hw⟩, Set.inter_subset_right, ?_⟩
        rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨fun x hx => h1 x hx.1, h2.mono Set.inter_subset_left⟩
        · exact Or.inr ⟨fun x hx => h1 x hx.1, h2.mono Set.inter_subset_left⟩
      · exact (hbound _ (hn w (ball_subset_closedBall hw)).2).1
    obtain ⟨C, hC0, hCdef⟩ : ∃ C : ℝ, 0 < C ∧ C = (1 + (2 / (2 * ε₀)) ^ 2) / 2 :=
      ⟨(1 + (2 / (2 * ε₀)) ^ 2) / 2, by positivity, rfl⟩
    have hC0' : C ≠ 0 := ne_of_gt hC0
    have huTLU : TendstoUniformlyOn (fun n w => chartFiniteMap (F n w))
        (fun w => chartFiniteMap (G w)) atTop (closedBall z r) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [hFev, Metric.tendstoUniformlyOn_iff.mp hunif (ε / C) (by positivity)]
        with n hn hn2 w hw
      obtain ⟨hFne, hFbd⟩ := hbound _ (hn w hw).2
      obtain ⟨hGne, hGbd⟩ := hbound _ (le_trans (by linarith) (hGfar w hw))
      have hnorm := norm_sub_le_sphericalDist_mul hGbd hFbd
      have hds : sphericalDist ((chartFiniteMap (G w) : ℂ) : ℂ̂)
          ((chartFiniteMap (F n w) : ℂ) : ℂ̂) = dist (G w) (F n w) := by
        rw [hcoe _ hGne, hcoe _ hFne]
        rfl
      rw [hds, ← hCdef] at hnorm
      calc dist (chartFiniteMap (G w)) (chartFiniteMap (F n w))
          = ‖chartFiniteMap (G w) - chartFiniteMap (F n w)‖ := dist_eq_norm _ _
        _ ≤ C * dist (G w) (F n w) := hnorm
        _ < C * (ε / C) := mul_lt_mul_of_pos_left (hn2 w hw) hC0
        _ = ε := by field_simp
    have hTLUb : TendstoLocallyUniformlyOn (fun n w => chartFiniteMap (F n w))
        (fun w => chartFiniteMap (G w)) atTop (ball z r) :=
      huTLU.tendstoLocallyUniformlyOn.mono ball_subset_closedBall
    have huGdiff : DifferentiableOn ℂ (fun w => chartFiniteMap (G w)) (ball z r) :=
      hTLUb.differentiableOn hudiff isOpen_ball
    have hballnhds : ball z r ∈ nhds z := isOpen_ball.mem_nhds (mem_ball_self hr)
    -- the chart formula for the limit
    have hG_eq : sphericalDeriv G z =
        2 * ‖deriv (fun w => chartFiniteMap (G w)) z‖ / (1 + ‖chartFiniteMap (G z)‖ ^ 2) := by
      refine sphericalDeriv_eq_of_eventuallyEq_coe ?_ (huGdiff.differentiableAt hballnhds)
      filter_upwards [hballnhds] with w hw
      have hfar : 2 * ε₀ ≤ dist (G w) (∞ : ℂ̂) :=
        le_trans (by linarith) (hGfar w (ball_subset_closedBall hw))
      exact (hcoe _ (hbound _ hfar).1).symm
    -- the chart formula for the members, eventually in `n`
    have hFn_eq : ∀ᶠ n in atTop, sphericalDeriv (F n) z =
        2 * ‖deriv (fun w => chartFiniteMap (F n w)) z‖ / (1 + ‖chartFiniteMap (F n z)‖ ^ 2) := by
      filter_upwards [hFev, hudiff] with n hn hdn
      refine sphericalDeriv_eq_of_eventuallyEq_coe ?_ (hdn.differentiableAt hballnhds)
      filter_upwards [hballnhds] with w hw
      exact (hcoe _ (hbound _ (hn w (ball_subset_closedBall hw)).2).1).symm
    -- convergence of values and derivatives of the chart readings at `z`
    have hval : Tendsto (fun n => chartFiniteMap (F n z)) atTop (𝓝 (chartFiniteMap (G z))) :=
      hTLUb.tendsto_at (mem_ball_self hr)
    have hder : Tendsto (fun n => deriv (fun w => chartFiniteMap (F n w)) z) atTop
        (𝓝 (deriv (fun w => chartFiniteMap (G w)) z)) :=
      (hTLUb.deriv hudiff isOpen_ball).tendsto_at (mem_ball_self hr)
    rw [hG_eq]
    have hlim := (hder.norm.const_mul 2).div ((hval.norm.pow 2).const_add 1) (by positivity)
    exact hlim.congr' (hFn_eq.mono fun n hn => hn.symm)
  by_cases hzi : g z = ∞
  · -- pass to the inversion; the spherical derivative is inversion-invariant
    have hol' : ∀ n, SphereHolomorphicOn (fun w => inversionGL • Fn n w) U := fun n =>
      (hol n).gl_smul inversionGL
    have hg' : TendstoLocallyUniformlyOn (fun n w => inversionGL • Fn n w)
        (fun w => inversionGL • g w) atTop U := by
      rw [Metric.tendstoLocallyUniformlyOn_iff] at hg ⊢
      intro ε hε x hx
      obtain ⟨t, ht, hev⟩ := hg ε hε x hx
      refine ⟨t, ht, hev.mono fun n hn y hy => ?_⟩
      exact lt_of_eq_of_lt (sphericalDist_inversionGL_smul (g y) (Fn n y)) (hn y hy)
    have hne : inversionGL • g z ≠ ∞ := by
      rw [hzi, inversionGL_smul_infty]
      exact OnePoint.coe_ne_infty 0
    have h := key _ _ hol' hg' hne
    have h2 : sphericalDeriv (fun w => inversionGL • g w) z = sphericalDeriv g z :=
      sphericalDeriv_inversionGL_smul g z
    rw [← h2]
    exact h.congr fun n => sphericalDeriv_inversionGL_smul (Fn n) z
  · exact key Fn g hol hg hzi

-- The proof is one long construction: the Zalcman max-trick produces members, centers and
-- scales, a quantitative spherical-derivative bound follows from maximality, and a
-- nested-subsequence diagonal over the growing balls `ball 0 (m + 1)` glues the limit.
set_option maxHeartbeats 400000 in
-- The diagonal recursion and the many `choose`-d data make the default heartbeat budget
-- insufficient, so it is raised (within the allowed limit).
/-- **Zalcman's rescaling lemma.** At a point of non-normality of a family
of sphere-holomorphic maps there are members `F k`, centers `z k → z₀`,
and scales `ρ k ↓ 0` whose affine rescalings converge locally uniformly on
all of `ℂ` to a sphere-holomorphic limit `g` with `g# (0) = 1` and
`g# ≤ 1` — in particular `g` is nonconstant. -/
theorem exists_zalcman_rescale {𝓕 : Set (ℂ → ℂ̂)} {U : Set ℂ}
    (hU : IsOpen U) (hol : ∀ F ∈ 𝓕, SphereHolomorphicOn F U) {z₀ : ℂ}
    (hz₀ : z₀ ∈ U) (hnot : ¬ IsNormalAt 𝓕 z₀) :
    ∃ (F : ℕ → ℂ → ℂ̂) (z : ℕ → ℂ) (ρ : ℕ → ℝ) (g : ℂ → ℂ̂),
      (∀ k, F k ∈ 𝓕) ∧ Tendsto z atTop (nhds z₀) ∧ (∀ k, 0 < ρ k) ∧
      Tendsto ρ atTop (nhds 0) ∧ SphereHolomorphicOn g Set.univ ∧
      sphericalDeriv g 0 = 1 ∧ (∀ ζ : ℂ, sphericalDeriv g ζ ≤ 1) ∧
      TendstoLocallyUniformlyOn
        (fun k => fun ζ => F k (z k + (ρ k : ℂ) * ζ)) g atTop Set.univ := by
  classical
  -- ## Setup: a closed ball of radius `2 r₀` around `z₀` inside `U`
  obtain ⟨r₀, hr₀pos, h2r₀U⟩ : ∃ r₀ : ℝ, 0 < r₀ ∧ closedBall z₀ (2 * r₀) ⊆ U := by
    obtain ⟨ε₀, hε₀, hball₀⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
    refine ⟨ε₀ / 4, by linarith, fun x hx => hball₀ ?_⟩
    rw [mem_closedBall] at hx
    rw [mem_ball]
    linarith
  -- the shrinking radii `r k = min r₀ (1/(k+1))`
  obtain ⟨r, hr_def⟩ : ∃ r : ℕ → ℝ, ∀ k, r k = min r₀ (1 / ((k : ℝ) + 1)) :=
    ⟨_, fun _ => rfl⟩
  have hrpos : ∀ k, 0 < r k := fun k => by
    rw [hr_def]; exact lt_min hr₀pos (by positivity)
  have hr_le_r₀ : ∀ k, r k ≤ r₀ := fun k => by rw [hr_def]; exact min_le_left _ _
  have hr_le_inv : ∀ k, r k ≤ 1 / ((k : ℝ) + 1) := fun k => by
    rw [hr_def]; exact min_le_right _ _
  have hballU : ∀ k, closedBall z₀ (r k) ⊆ U := fun k =>
    (closedBall_subset_closedBall (by linarith [hr_le_r₀ k, hr₀pos])).trans h2r₀U
  -- ## Seeds: members with blowing-up spherical derivative near `z₀`
  have hsel : ∀ k : ℕ, ∃ F ∈ 𝓕, ∃ w : ℂ, ‖w - z₀‖ < r k / 2 ∧
      ((k : ℝ) + 1) * (2 / r k) < sphericalDeriv F w := fun k =>
    exists_sphericalDeriv_gt_of_not_isNormalAt hU hol hz₀ hnot _ (half_pos (hrpos k))
  choose F₀ hF₀ w hw hMw using hsel
  -- ## Maximize `(r k − ‖·−z₀‖) · (F₀ k)#` over the closed ball `closedBall z₀ (r k)`
  have hmaxsel : ∀ k : ℕ, ∃ zk ∈ closedBall z₀ (r k),
      IsMaxOn (fun x => (r k - ‖x - z₀‖) * sphericalDeriv (F₀ k) x)
        (closedBall z₀ (r k)) zk := by
    intro k
    refine (isCompact_closedBall z₀ (r k)).exists_isMaxOn
      ⟨z₀, mem_closedBall_self (hrpos k).le⟩ ?_
    exact ((continuous_const.sub
        ((continuous_id.sub continuous_const).norm)).continuousOn).mul
      (((hol _ (hF₀ k)).continuousOn_sphericalDeriv).mono (hballU k))
  choose z hz hzmax using hmaxsel
  -- abbreviations: derivative `D`, gap `s`, max value `L`, scale `ρ`
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, ∀ k, D k = sphericalDeriv (F₀ k) (z k) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, ∀ k, s k = r k - ‖z k - z₀‖ := ⟨_, fun _ => rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℕ → ℝ, ∀ k, L k = s k * D k := ⟨_, fun _ => rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → ℝ, ∀ k, ρ k = 1 / D k := ⟨_, fun _ => rfl⟩
  have hzdist : ∀ k, ‖z k - z₀‖ ≤ r k := fun k => by
    have := hz k; rwa [mem_closedBall, dist_eq_norm] at this
  -- ## The max value satisfies `L k ≥ k + 1`, so `L → ∞`
  have hLlb : ∀ k : ℕ, (k : ℝ) + 1 ≤ L k := by
    intro k
    have hwmem : w k ∈ closedBall z₀ (r k) := by
      rw [mem_closedBall, dist_eq_norm]; linarith [hw k, hrpos k]
    have h1 : ((k : ℝ) + 1) = (r k / 2) * (((k : ℝ) + 1) * (2 / r k)) := by
      field_simp [(hrpos k).ne']
    have h2 : (r k / 2) * (((k : ℝ) + 1) * (2 / r k))
        ≤ (r k - ‖w k - z₀‖) * sphericalDeriv (F₀ k) (w k) :=
      mul_le_mul (by linarith [hw k]) (hMw k).le
        (mul_nonneg (by positivity) (div_pos two_pos (hrpos k)).le)
        (by linarith [hw k, hrpos k])
    have h3 : (r k - ‖w k - z₀‖) * sphericalDeriv (F₀ k) (w k) ≤ L k := by
      rw [hL k, hs k, hD k]
      exact hzmax k hwmem
    linarith
  have hLpos : ∀ k, 0 < L k := fun k => lt_of_lt_of_le (by positivity) (hLlb k)
  have hsdnn : ∀ (G : ℂ → ℂ̂) (x : ℂ), 0 ≤ sphericalDeriv G x := fun G x => norm_nonneg _
  have hDnn : ∀ k, 0 ≤ D k := fun k => by rw [hD k]; exact hsdnn _ _
  have hsnn : ∀ k, 0 ≤ s k := fun k => by rw [hs k]; linarith [hzdist k]
  have hDpos : ∀ k, 0 < D k := by
    intro k
    rcases (hDnn k).lt_or_eq with h | h
    · exact h
    · exfalso
      have h2 := hLpos k
      rw [hL k, ← h, mul_zero] at h2
      exact lt_irrefl 0 h2
  have hspos : ∀ k, 0 < s k := by
    intro k
    rcases (hsnn k).lt_or_eq with h | h
    · exact h
    · exfalso
      have h2 := hLpos k
      rw [hL k, ← h, zero_mul] at h2
      exact lt_irrefl 0 h2
  have hρpos : ∀ k, 0 < ρ k := fun k => by
    rw [hρ k]; exact one_div_pos.mpr (hDpos k)
  have hρL : ∀ k, ρ k * L k = s k := by
    intro k
    rw [hρ k, hL k]
    field_simp [(hDpos k).ne']
  have hs_le_r : ∀ k, s k ≤ r k := fun k => by
    rw [hs k]; linarith [norm_nonneg (z k - z₀)]
  have hLtop : Tendsto L atTop atTop :=
    tendsto_atTop_mono hLlb
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  -- ## centers converge to `z₀`, scales to `0`
  have hz_tend : Tendsto z atTop (nhds z₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact (mem_closedBall.mp (hz k)).trans (hr_le_inv k)
  have hρ_tend : Tendsto ρ atTop (nhds 0) := by
    have hlim : Tendsto (fun k : ℕ => r₀ * (1 / ((k : ℝ) + 1))) atTop (nhds 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul r₀
      simpa using h
    refine squeeze_zero (fun k => (hρpos k).le) (fun k => ?_) hlim
    have h1 : ρ k * ((k : ℝ) + 1) ≤ ρ k * L k :=
      mul_le_mul_of_nonneg_left (hLlb k) (hρpos k).le
    rw [hρL k] at h1
    rw [mul_one_div, le_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
    have h2 : s k ≤ r₀ := (hs_le_r k).trans (hr_le_r₀ k)
    linarith
  -- norm of the complexified (real, positive) scale
  have hnormρ : ∀ k, ‖((ρ k : ℝ) : ℂ)‖ = ρ k := fun k => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hρpos k)]
  -- displacement estimate for the rescaled point
  have hcalc : ∀ (k : ℕ) (ζ : ℂ) (T : ℝ), ‖ζ‖ ≤ T →
      ‖z k + ((ρ k : ℝ) : ℂ) * ζ - z₀‖ ≤ ‖z k - z₀‖ + ρ k * T := by
    intro k ζ T hT
    have heq : z k + ((ρ k : ℝ) : ℂ) * ζ - z₀ = (z k - z₀) + ((ρ k : ℝ) : ℂ) * ζ := by
      ring
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hnormρ k]
    have := mul_le_mul_of_nonneg_left hT (hρpos k).le
    linarith
  -- the rescalings have spherical derivative exactly `1` at the origin
  have hone : ∀ k : ℕ,
      sphericalDeriv (fun ζ => F₀ k (z k + ((ρ k : ℝ) : ℂ) * ζ)) 0 = 1 := by
    intro k
    rw [sphericalDeriv_comp_affine, mul_zero, add_zero, hnormρ k, ← hD k, hρ k]
    exact one_div_mul_cancel (hDpos k).ne'
  -- ## The key bound: rescaled spherical derivatives are eventually `≤ 1 + ε` on `‖ζ‖ ≤ R`
  have key : ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ ζ : ℂ, ‖ζ‖ ≤ R →
      sphericalDeriv (fun ζ' => F₀ k (z k + ((ρ k : ℝ) : ℂ) * ζ')) ζ ≤ 1 + ε := by
    intro R hR ε hε
    filter_upwards [hLtop.eventually_ge_atTop (R + 1),
      hLtop.eventually_ge_atTop (R * (1 + ε) / ε)] with k hk1 hk2 ζ hζ
    have hRL : R * (1 + ε) ≤ ε * L k := by
      rw [div_le_iff₀ hε] at hk2
      linarith
    have hRltL : R < L k := by linarith
    rw [sphericalDeriv_comp_affine, hnormρ k]
    -- the rescaled point stays inside the closed ball, by `ρ k · R < s k`
    have hρR : ρ k * R < s k := by
      have h5 := mul_lt_mul_of_pos_left hRltL (hρpos k)
      rwa [hρL k] at h5
    have hymem : z k + ((ρ k : ℝ) : ℂ) * ζ ∈ closedBall z₀ (r k) := by
      rw [mem_closedBall, dist_eq_norm]
      have h6 := hcalc k ζ R hζ
      have h7 := hs k
      linarith
    have hgap : s k - ρ k * R ≤ r k - ‖z k + ((ρ k : ℝ) : ℂ) * ζ - z₀‖ := by
      have h6 := hcalc k ζ R hζ
      have h7 := hs k
      linarith
    -- maximality at `z k` bounds the derivative at the rescaled point
    have hmaxy : (r k - ‖z k + ((ρ k : ℝ) : ℂ) * ζ - z₀‖)
        * sphericalDeriv (F₀ k) (z k + ((ρ k : ℝ) : ℂ) * ζ) ≤ L k := by
      rw [hL k, hs k, hD k]
      exact hzmax k hymem
    have hstep1 : (s k - ρ k * R)
        * sphericalDeriv (F₀ k) (z k + ((ρ k : ℝ) : ℂ) * ζ) ≤ L k :=
      le_trans (mul_le_mul_of_nonneg_right hgap (hsdnn _ _)) hmaxy
    have hstep2 : ρ k * ((s k - ρ k * R)
        * sphericalDeriv (F₀ k) (z k + ((ρ k : ℝ) : ℂ) * ζ)) ≤ s k := by
      calc ρ k * ((s k - ρ k * R)
            * sphericalDeriv (F₀ k) (z k + ((ρ k : ℝ) : ℂ) * ζ))
          ≤ ρ k * L k := mul_le_mul_of_nonneg_left hstep1 (hρpos k).le
        _ = s k := hρL k
    have hεσ : s k ≤ (1 + ε) * (s k - ρ k * R) := by
      have h3 : ρ k * (R * (1 + ε)) ≤ ρ k * (ε * L k) :=
        mul_le_mul_of_nonneg_left hRL (hρpos k).le
      have h4 : ρ k * (ε * L k) = ε * s k := by
        rw [← hρL k]; ring
      nlinarith [h3, h4, hspos k, hρpos k]
    have hfin : ρ k * sphericalDeriv (F₀ k) (z k + ((ρ k : ℝ) : ℂ) * ζ)
        * (s k - ρ k * R) ≤ (1 + ε) * (s k - ρ k * R) := by
      have h8 : ρ k * sphericalDeriv (F₀ k) (z k + ((ρ k : ℝ) : ℂ) * ζ)
            * (s k - ρ k * R)
          = ρ k * ((s k - ρ k * R)
            * sphericalDeriv (F₀ k) (z k + ((ρ k : ℝ) : ℂ) * ζ)) := by
        ring
      rw [h8]
      exact le_trans hstep2 hεσ
    exact le_of_mul_le_mul_right hfin (by linarith)
  -- ## restriction of sphere-holomorphy to open subsets
  have holo_mono : ∀ (G : ℂ → ℂ̂) (V W : Set ℂ), SphereHolomorphicOn G V → IsOpen W →
      W ⊆ V → SphereHolomorphicOn G W := by
    intro G V W hG hW hWV x hx
    obtain ⟨V', hV'o, hxV', hV'V, hcase⟩ := hG x (hWV hx)
    refine ⟨V' ∩ W, hV'o.inter hW, ⟨hxV', hx⟩, Set.inter_subset_right, ?_⟩
    rcases hcase with ⟨hne, hd⟩ | ⟨hne, hd⟩
    · exact Or.inl ⟨fun y hy => hne y hy.1, hd.mono Set.inter_subset_left⟩
    · exact Or.inr ⟨fun y hy => hne y hy.1, hd.mono Set.inter_subset_left⟩
  -- eventual sphere-holomorphy of the rescalings on each ball `ball 0 (m+1)`
  have hev_holo : ∀ m : ℕ, ∀ᶠ k in atTop,
      SphereHolomorphicOn (fun ζ => F₀ k (z k + ((ρ k : ℝ) : ℂ) * ζ))
        (ball 0 ((m : ℝ) + 1)) := by
    intro m
    filter_upwards [hLtop.eventually_ge_atTop ((m : ℝ) + 1)] with k hk
    refine holo_mono _ _ _ ((hol _ (hF₀ k)).comp_affine (z k) ((ρ k : ℂ)))
      isOpen_ball ?_
    intro ζ hζ
    have hζ' : ‖ζ‖ ≤ (m : ℝ) + 1 := (mem_ball_zero_iff.mp hζ).le
    have h1 := hcalc k ζ ((m : ℝ) + 1) hζ'
    have h2 : ρ k * ((m : ℝ) + 1) ≤ s k := by
      rw [← hρL k]
      exact mul_le_mul_of_nonneg_left hk (hρpos k).le
    have h3 := hs k
    have h4 := hr_le_r₀ k
    have h5 := hzdist k
    change z k + ((ρ k : ℝ) : ℂ) * ζ ∈ U
    refine h2r₀U ?_
    rw [mem_closedBall, dist_eq_norm]
    linarith
  -- ## stage thresholds: past `K m` the rescalings are sphere-holomorphic and `# ≤ 2`
  have hKsel : ∀ m : ℕ, ∃ N : ℕ, ∀ k, N ≤ k →
      SphereHolomorphicOn (fun ζ => F₀ k (z k + ((ρ k : ℝ) : ℂ) * ζ))
        (ball 0 ((m : ℝ) + 1)) ∧
      ∀ ζ : ℂ, ‖ζ‖ ≤ (m : ℝ) + 1 →
        sphericalDeriv (fun ζ' => F₀ k (z k + ((ρ k : ℝ) : ℂ) * ζ')) ζ ≤ 2 := by
    intro m
    have h2 : ∀ᶠ k in atTop, ∀ ζ : ℂ, ‖ζ‖ ≤ (m : ℝ) + 1 →
        sphericalDeriv (fun ζ' => F₀ k (z k + ((ρ k : ℝ) : ℂ) * ζ')) ζ ≤ 2 := by
      filter_upwards [key ((m : ℝ) + 1) (by positivity) 1 one_pos] with k hk ζ hζ
      have := hk ζ hζ
      linarith
    exact eventually_atTop.mp ((hev_holo m).and h2)
  choose K hK using hKsel
  -- ## per-stage normality of the eventual rescaled family, via Marty
  have hnormal : ∀ m : ℕ, IsNormal
      {G : ℂ → ℂ̂ | ∃ k, K m ≤ k ∧ G = fun ζ => F₀ k (z k + ((ρ k : ℝ) : ℂ) * ζ)}
      (ball 0 ((m : ℝ) + 1)) := by
    intro m
    refine isNormal_of_sphericalDeriv_le (M := 2) isOpen_ball ?_ ?_
    · rintro G ⟨k, hk, rfl⟩
      exact (hK m k hk).1
    · rintro G ⟨k, hk, rfl⟩ ζ hζ
      exact (hK m k hk).2 ζ (mem_ball_zero_iff.mp hζ).le
  -- ## per-stage extraction kernel (thresholds folded in via `max`)
  have step : ∀ (m : ℕ) (h : ℕ → ℕ), ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ g0 : ℂ → ℂ̂,
      TendstoLocallyUniformlyOn
        (fun j ζ => F₀ (max (h (ψ j)) (K m))
          (z (max (h (ψ j)) (K m)) + ((ρ (max (h (ψ j)) (K m)) : ℝ) : ℂ) * ζ))
        g0 atTop (ball 0 ((m : ℝ) + 1)) := by
    intro m h
    obtain ⟨φ, hφ, gst, hgst⟩ := hnormal m fun n =>
      ⟨fun ζ => F₀ (max (h n) (K m))
          (z (max (h n) (K m)) + ((ρ (max (h n) (K m)) : ℝ) : ℂ) * ζ),
        max (h n) (K m), le_max_right _ _, rfl⟩
    exact ⟨φ, hφ, gst, hgst⟩
  choose ψ hψ g0 hg0 using step
  -- ## nested subsequences and the diagonal (mirrors `montel_caratheodory`)
  let τ : ℕ → ℕ → ℕ := fun m =>
    Nat.rec (motive := fun _ => ℕ → ℕ) (ψ 0 id) (fun i ih => ih ∘ ψ (i + 1) ih) m
  let G : ℕ → ℂ → ℂ̂ := fun m =>
    Nat.casesOn (motive := fun _ => ℂ → ℂ̂) m (g0 0 id) (fun i => g0 (i + 1) (τ i))
  have τ_mono : ∀ m, StrictMono (τ m) := by
    intro m
    induction m with
    | zero => exact hψ 0 id
    | succ i ih => exact ih.comp (hψ (i + 1) (τ i))
  -- TLU transfers along eventual equality of the sequence
  have tlu_congr_ev : ∀ {F₁ F₂ : ℕ → ℂ → ℂ̂} {gg : ℂ → ℂ̂} {S : Set ℂ},
      TendstoLocallyUniformlyOn F₁ gg atTop S → (∀ᶠ n in atTop, F₁ n = F₂ n) →
      TendstoLocallyUniformlyOn F₂ gg atTop S := by
    intro F₁ F₂ gg S h1 hag u hu x hx
    obtain ⟨t, ht, hev⟩ := h1 u hu x hx
    refine ⟨t, ht, ?_⟩
    filter_upwards [hev, hag] with n hn he y hy
    rw [← he]
    exact hn y hy
  have τ_tlu : ∀ m, TendstoLocallyUniformlyOn
      (fun j ζ => F₀ (τ m j) (z (τ m j) + ((ρ (τ m j) : ℝ) : ℂ) * ζ))
      (G m) atTop (ball 0 ((m : ℝ) + 1)) := by
    have hcollapse : ∀ (m : ℕ) (h : ℕ → ℕ), (∀ n, n ≤ h n) → ∀ᶠ j in atTop,
        (fun ζ => F₀ (max (h (ψ m h j)) (K m))
          (z (max (h (ψ m h j)) (K m)) + ((ρ (max (h (ψ m h j)) (K m)) : ℝ) : ℂ) * ζ))
        = fun ζ => F₀ (h (ψ m h j))
            (z (h (ψ m h j)) + ((ρ (h (ψ m h j)) : ℝ) : ℂ) * ζ) := by
      intro m h hh
      filter_upwards [eventually_ge_atTop (K m)] with j hj
      have hmx : max (h (ψ m h j)) (K m) = h (ψ m h j) :=
        max_eq_left (hj.trans ((hψ m h).le_apply.trans (hh _)))
      rw [hmx]
    intro m
    cases m with
    | zero => exact tlu_congr_ev (hg0 0 id) (hcollapse 0 id fun n => le_rfl)
    | succ i =>
      exact tlu_congr_ev (hg0 (i + 1) (τ i))
        (hcollapse (i + 1) (τ i) fun n => (τ_mono i).le_apply)
  have τ_refine : ∀ i m, ∃ e : ℕ → ℕ, (∀ k, k ≤ e k) ∧ ∀ k, τ (i + m) k = τ i (e k) := by
    intro i m
    induction m with
    | zero => exact ⟨id, fun k => le_rfl, fun k => rfl⟩
    | succ m ih =>
      obtain ⟨e, he, heq⟩ := ih
      exact ⟨fun k => e (ψ (i + m + 1) (τ (i + m)) k),
        fun k => le_trans (hψ (i + m + 1) (τ (i + m))).le_apply (he _),
        fun k => heq (ψ (i + m + 1) (τ (i + m)) k)⟩
  let d : ℕ → ℕ := fun k => τ k k
  have d_mono : StrictMono d := by
    apply strictMono_nat_of_lt_succ
    intro k
    calc d k = τ k k := rfl
      _ < τ k (k + 1) := τ_mono k (Nat.lt_succ_self k)
      _ ≤ τ k (ψ (k + 1) (τ k) (k + 1)) :=
          (τ_mono k).monotone (hψ (k + 1) (τ k)).le_apply
      _ = d (k + 1) := rfl
  have d_sub : ∀ m k, m ≤ k → ∃ n, k ≤ n ∧ d k = τ m n := by
    intro m k hmk
    obtain ⟨e, he, heq⟩ := τ_refine m (k - m)
    have hk : m + (k - m) = k := Nat.add_sub_cancel' hmk
    have h2 := heq k
    rw [hk] at h2
    exact ⟨e k, he k, h2⟩
  -- the diagonal converges locally uniformly on every stage ball
  have d_tlu : ∀ m, TendstoLocallyUniformlyOn
      (fun k ζ => F₀ (d k) (z (d k) + ((ρ (d k) : ℝ) : ℂ) * ζ))
      (G m) atTop (ball 0 ((m : ℝ) + 1)) := by
    intro m v hv x hx
    obtain ⟨t, ht, hF⟩ := τ_tlu m v hv x hx
    refine ⟨t, ht, ?_⟩
    rw [eventually_atTop] at hF ⊢
    obtain ⟨N, hN⟩ := hF
    refine ⟨max m N, fun k hk => ?_⟩
    obtain ⟨n, hkn, hdn⟩ := d_sub m k (le_trans (le_max_left m N) hk)
    intro y hy
    have h5 := hN n (le_trans (le_trans (le_max_right m N) hk) hkn) y hy
    change (G m y, F₀ (d k) (z (d k) + ((ρ (d k) : ℝ) : ℂ) * y)) ∈ v
    rw [hdn]
    exact h5
  -- ## glue the stage limits into a single limit function
  have hRball : ∀ ζ : ℂ, ∃ m : ℕ, ζ ∈ ball (0 : ℂ) ((m : ℝ) + 1) := by
    intro ζ
    obtain ⟨m, hm⟩ := exists_nat_gt ‖ζ‖
    exact ⟨m, mem_ball_zero_iff.mpr (by linarith)⟩
  have glex : ∀ ζ : ℂ, ∃ wv : ℂ̂, ∀ m : ℕ,
      ζ ∈ ball (0 : ℂ) ((m : ℝ) + 1) → wv = G m ζ := by
    intro ζ
    obtain ⟨i, hi⟩ := hRball ζ
    refine ⟨G i ζ, fun m hm => ?_⟩
    exact tendsto_nhds_unique ((d_tlu i).tendsto_at hi) ((d_tlu m).tendsto_at hm)
  choose gl hgl using glex
  -- locally uniform convergence on all of `ℂ`
  have final_tlu : TendstoLocallyUniformlyOn
      (fun k ζ => F₀ (d k) (z (d k) + ((ρ (d k) : ℝ) : ℂ) * ζ)) gl atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro Kc hKcU hKc
    obtain ⟨RK, hRK⟩ := hKc.isBounded.subset_ball 0
    obtain ⟨m, hm⟩ := exists_nat_gt RK
    have hKb : Kc ⊆ ball (0 : ℂ) ((m : ℝ) + 1) :=
      hRK.trans (ball_subset_ball (by linarith))
    have h1 := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp
      (d_tlu m) Kc hKb hKc
    exact h1.congr_right fun ζ hζ => (hgl ζ m (hKb hζ)).symm
  -- index-shifted diagonals still converge (TLU is `atTop`-insensitive)
  have tlu_shift : ∀ {Fn : ℕ → ℂ → ℂ̂} {gg : ℂ → ℂ̂} {S : Set ℂ} (N : ℕ),
      TendstoLocallyUniformlyOn Fn gg atTop S →
      TendstoLocallyUniformlyOn (fun n => Fn (n + N)) gg atTop S := by
    intro Fn gg S N h u hu x hx
    obtain ⟨t, ht, hev⟩ := h u hu x hx
    exact ⟨t, ht, (tendsto_add_atTop_nat N).eventually hev⟩
  have d_ge : ∀ k, k ≤ d k := fun k => d_mono.le_apply
  have shifted_hol : ∀ m n : ℕ, SphereHolomorphicOn
      (fun ζ => F₀ (d (n + K m)) (z (d (n + K m)) + ((ρ (d (n + K m)) : ℝ) : ℂ) * ζ))
      (ball 0 ((m : ℝ) + 1)) := fun m n =>
    (hK m (d (n + K m)) (le_trans (Nat.le_add_left (K m) n) (d_ge (n + K m)))).1
  have shifted_tlu : ∀ m : ℕ, TendstoLocallyUniformlyOn
      (fun n ζ => F₀ (d (n + K m)) (z (d (n + K m)) + ((ρ (d (n + K m)) : ℝ) : ℂ) * ζ))
      gl atTop (ball 0 ((m : ℝ) + 1)) := fun m =>
    (tlu_shift (K m) (d_tlu m)).congr_right fun ζ hζ => (hgl ζ m hζ).symm
  -- ## the limit is sphere-holomorphic on all of `ℂ`
  have hgl_hol : SphereHolomorphicOn gl Set.univ := by
    intro ζ _
    obtain ⟨m, hm⟩ := hRball ζ
    have hball : SphereHolomorphicOn gl (ball 0 ((m : ℝ) + 1)) :=
      sphereHolomorphicOn_of_tendstoLocallyUniformlyOn isOpen_ball
        (shifted_hol m) (shifted_tlu m)
    obtain ⟨V, hVo, hζV, hVsub, hcase⟩ := hball ζ hm
    exact ⟨V, hVo, hζV, Set.subset_univ V, hcase⟩
  -- ## normalization `gl# 0 = 1`
  have hgl0 : sphericalDeriv gl 0 = 1 := by
    have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) (((0 : ℕ) : ℝ) + 1) :=
      mem_ball_zero_iff.mpr (by simp)
    have htend := tendsto_sphericalDeriv_of_tendstoLocallyUniformlyOn isOpen_ball
      (shifted_hol 0) (shifted_tlu 0) h0mem
    have h2 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds (sphericalDeriv gl 0)) :=
      Filter.Tendsto.congr (fun n => hone (d (n + K 0))) htend
    exact tendsto_nhds_unique h2 tendsto_const_nhds
  -- ## the bound `gl# ≤ 1`
  have hgl_le : ∀ ζ : ℂ, sphericalDeriv gl ζ ≤ 1 := by
    intro ζ
    obtain ⟨m, hm⟩ := hRball ζ
    have htend := tendsto_sphericalDeriv_of_tendstoLocallyUniformlyOn isOpen_ball
      (shifted_hol m) (shifted_tlu m) hm
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    have hcomp : Tendsto (fun n => d (n + K m)) atTop atTop :=
      d_mono.tendsto_atTop.comp (tendsto_add_atTop_nat (K m))
    have hev2 : ∀ᶠ n in atTop, sphericalDeriv
        (fun ζ' => F₀ (d (n + K m))
          (z (d (n + K m)) + ((ρ (d (n + K m)) : ℝ) : ℂ) * ζ')) ζ ≤ 1 + ε := by
      filter_upwards [hcomp.eventually (key ((m : ℝ) + 1) (by positivity) ε hε)] with n hn
      exact hn ζ (mem_ball_zero_iff.mp hm).le
    exact le_of_tendsto htend hev2
  -- ## package
  exact ⟨fun j => F₀ (d j), fun j => z (d j), fun j => ρ (d j), gl,
    fun j => hF₀ (d j), hz_tend.comp d_mono.tendsto_atTop, fun j => hρpos (d j),
    hρ_tend.comp d_mono.tendsto_atTop, hgl_hol, hgl0, hgl_le, final_tlu⟩

end NoWanderingDomains
