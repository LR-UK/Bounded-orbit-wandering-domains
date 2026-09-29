module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

public import EremenkoLyubichConstant.Tract

@[expose] public section

/-!
# Real-variable consequences of the tract estimate

This module records the integration inequality used in Corollary 2.3.  It is stated at
the exact level needed independently of the complex-analytic construction of the inverse tract ray.
-/

open Set Filter MeasureTheory

namespace EremenkoLyubichConstant

noncomputable section

/-- The pullback density of the half-plane metric under a tract equivalence.  This is
the quantity denoted `rho_T` in Corollary 2.2 of the paper. -/
def tractHyperbolicDensity {T : Set ℂ} {rho : ℝ} (e : TractEquiv T rho) (zeta : ℂ) : ℝ :=
  ‖deriv e.toFun zeta‖ / ((e.toFun zeta).re - rho)

/-- Corollary 2.2: the hyperbolic density of a logarithmic tract is at least one half. -/
theorem one_half_le_tractHyperbolicDensity
    {T : Set ℂ} {rho : ℝ} (e : TractEquiv T rho) {zeta : ℂ}
    (hzeta : zeta ∈ T) (hexp : Set.InjOn Complex.exp T) :
    (1 : ℝ) / 2 ≤ tractHyperbolicDensity e zeta := by
  have hpos : 0 < (e.toFun zeta).re - rho := sub_pos.mpr (e.toFun_maps hzeta)
  rw [tractHyperbolicDensity, le_div_iff₀ hpos]
  have hmain := expansion_for_tract e hzeta hexp
  linarith

/-- Integrating the inverse-tract derivative bound along a positive real ray. -/
theorem inverse_ray_distance_bound
    {psi : ℝ → ℂ} {t : ℝ}
    (ht : 1 ≤ t)
    (hcont : ContinuousOn psi (Set.Icc 1 t))
    (hderiv : ∀ x ∈ Set.Ioo 1 t, HasDerivAt psi (deriv psi x) x)
    (hbound : ∀ x ∈ Set.Icc 1 t, ‖deriv psi x‖ ≤ 2 / x) :
    ‖psi t - psi 1‖ ≤ 2 * Real.log t := by
  have hpos : ∀ x ∈ Set.Icc 1 t, (0 : ℝ) < x := by
    intro x hx
    have hx1 : 1 ≤ x := hx.1
    linarith
  have hint : IntervalIntegrable (fun x : ℝ => (2 / x : ℝ)) volume 1 t := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div₀ continuousOn_const continuousOn_id
    intro x hx
    apply ne_of_gt
    exact hpos x (by simpa [Set.uIcc_of_le ht] using hx)
  have hdiff : ‖psi t - psi 1‖ ≤ ∫ x in 1..t, (2 / x : ℝ) := by
    apply norm_sub_le_integral_of_norm_deriv_le_of_le ht hcont
    · intro x hx
      exact (hderiv x hx).differentiableAt.differentiableWithinAt
    · filter_upwards [] with x hx
      exact hbound x ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    · exact hint
  calc
    ‖psi t - psi 1‖ ≤ ∫ x in 1..t, (2 / x : ℝ) := hdiff
    _ = 2 * Real.log t := by
      simp_rw [div_eq_mul_inv]
      rw [intervalIntegral.integral_const_mul,
        integral_inv_of_pos (by norm_num) (lt_of_lt_of_le (by norm_num) ht)]
      simp

/-- The pointwise logarithmic-growth conclusion in the proof of Corollary 2.3.
The crossing assumption isolates the elementary intermediate-value step used in the paper. -/
theorem lower_order_log_coordinate_witness
    {psi : ℝ → ℂ} {sigma0 : ℝ}
    (hcont : ContinuousOn psi (Set.Ici 1))
    (hderiv : ∀ x, 1 < x → HasDerivAt psi (deriv psi x) x)
    (hbound : ∀ x, 1 ≤ x → ‖deriv psi x‖ ≤ 2 / x)
    (hcross : ∀ sigma, sigma0 ≤ sigma → ∃ t, 1 ≤ t ∧ (psi t).re = sigma) :
    ∀ sigma, sigma0 ≤ sigma → ∃ t, 1 ≤ t ∧ (psi t).re = sigma ∧
      sigma / 2 - (psi 1).re / 2 ≤ Real.log t := by
  intro sigma hsigma
  obtain ⟨t, ht, hre⟩ := hcross sigma hsigma
  refine ⟨t, ht, hre, ?_⟩
  have hdist : ‖psi t - psi 1‖ ≤ 2 * Real.log t :=
    inverse_ray_distance_bound ht (hcont.mono fun _ hx ↦ hx.1)
      (fun x hx => hderiv x hx.1) (fun x hx => hbound x hx.1)
  have hre_le : sigma - (psi 1).re ≤ ‖psi t - psi 1‖ := by
    rw [← hre, ← Complex.sub_re]
    exact le_trans (le_abs_self _) (Complex.abs_re_le_norm (psi t - psi 1))
  linarith

/-- A continuous curve whose real part tends to positive infinity crosses every sufficiently
far-right vertical line.  This is the intermediate-value step in Corollary 2.3. -/
theorem eventually_crosses_vertical_lines
    {psi : ℝ → ℂ} (hcont : ContinuousOn psi (Set.Ici 1))
    (hescape : Tendsto (fun t ↦ (psi t).re) atTop atTop) :
    ∀ sigma, (psi 1).re ≤ sigma → ∃ t, 1 ≤ t ∧ (psi t).re = sigma := by
  intro sigma hsigma
  have hevRe : {t : ℝ | sigma ≤ (psi t).re} ∈ atTop :=
    hescape (eventually_ge_atTop sigma)
  have hevT : {t : ℝ | 1 ≤ t} ∈ atTop := eventually_ge_atTop 1
  obtain ⟨t, ht, hRe⟩ := (show ∃ t, 1 ≤ t ∧ sigma ≤ (psi t).re from
    Filter.nonempty_of_mem (Filter.inter_mem hevT hevRe))
  have himage : sigma ∈ (fun x ↦ (psi x).re) '' Set.Icc 1 t :=
    intermediate_value_Icc ht
      (Complex.continuous_re.comp_continuousOn hcont |>.mono fun _ hx ↦ hx.1) ⟨hsigma, hRe⟩
  obtain ⟨x, hx, hxeq⟩ := himage
  exact ⟨x, hx.1, hxeq⟩

/-- Corollary 2.3 at its natural existential level: on every sufficiently far-right
vertical line there is a tract point with logarithmic image at least linear in the line's
real coordinate. -/
theorem lower_order_log_coordinate_of_re_escape
    {psi : ℝ → ℂ}
    (hcont : ContinuousOn psi (Set.Ici 1))
    (hderiv : ∀ x, 1 < x → HasDerivAt psi (deriv psi x) x)
    (hbound : ∀ x, 1 ≤ x → ‖deriv psi x‖ ≤ 2 / x)
    (hescape : Tendsto (fun t ↦ (psi t).re) atTop atTop) :
    ∃ gamma > 0, ∃ sigma0 > 0, ∀ sigma ≥ sigma0,
      ∃ t, 1 ≤ t ∧ (psi t).re = sigma ∧ sigma / 2 - gamma ≤ Real.log t := by
  let gamma : ℝ := max ((psi 1).re / 2) 0 + 1
  let sigma0 : ℝ := max (psi 1).re 0 + 1
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    linarith [le_max_right ((psi 1).re / 2) 0]
  have hsigma0 : 0 < sigma0 := by
    dsimp [sigma0]
    linarith [le_max_right (psi 1).re 0]
  refine ⟨gamma, hgamma, sigma0, hsigma0, ?_⟩
  intro sigma hsigma
  have hbase : (psi 1).re ≤ sigma := by
    have : (psi 1).re ≤ sigma0 := by
      dsimp [sigma0]
      linarith [le_max_left (psi 1).re 0]
    exact this.trans hsigma
  obtain ⟨t, ht, hre, hlog⟩ :=
    lower_order_log_coordinate_witness hcont hderiv hbound
      (eventually_crosses_vertical_lines hcont hescape) sigma hbase
  refine ⟨t, ht, hre, ?_⟩
  have hgam : (psi 1).re / 2 ≤ gamma := by
    dsimp [gamma]
    linarith [le_max_left ((psi 1).re / 2) 0]
  linarith

/-- The inverse image under a tract chart of the horizontal ray based at `rho`. -/
def tractInverseRay {T : Set ℂ} {rho : ℝ} (e : TractEquiv T rho) (t : ℝ) : ℂ :=
  e.invFun ((t : ℂ) + (rho : ℂ))

/-- The inverse tract ray is continuous while its parameter is positive. -/
theorem continuousOn_tractInverseRay {T : Set ℂ} {rho : ℝ} (e : TractEquiv T rho) :
    ContinuousOn (tractInverseRay e) (Set.Ioi 0) := by
  intro t ht
  change ContinuousWithinAt (fun x : ℝ ↦ e.invFun ((x : ℂ) + (rho : ℂ)))
    (Set.Ioi 0) t
  change 0 < t at ht
  have harg : (t : ℂ) + (rho : ℂ) ∈ rightHalfPlane rho := by
    simp only [rightHalfPlane, Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re]
    linarith
  have hinv := e.differentiableOn_invFun.differentiableAt
    (isOpen_rightHalfPlane rho |>.mem_nhds harg)
  have hinner : ContinuousAt (fun x : ℝ ↦ (x : ℂ) + (rho : ℂ)) t := by fun_prop
  have hcomp : ContinuousAt (e.invFun ∘ fun x : ℝ ↦ (x : ℂ) + (rho : ℂ)) t :=
    hinv.continuousAt.comp_of_eq hinner rfl
  simpa [Function.comp_def] using hcomp.continuousWithinAt

/-- The real derivative of the inverse tract ray is the complex derivative of the inverse
chart evaluated on the ray. -/
theorem hasDerivAt_tractInverseRay {T : Set ℂ} {rho : ℝ} (e : TractEquiv T rho)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (tractInverseRay e) (deriv e.invFun ((t : ℂ) + (rho : ℂ))) t := by
  change HasDerivAt (fun x : ℝ ↦ e.invFun ((x : ℂ) + (rho : ℂ)))
    (deriv e.invFun ((t : ℂ) + (rho : ℂ))) t
  have harg : ((t + rho : ℝ) : ℂ) ∈ rightHalfPlane rho := by
    simp only [rightHalfPlane, Set.mem_ofPred_eq, Complex.ofReal_re]
    linarith
  have hinv : HasDerivAt e.invFun (deriv e.invFun ((t + rho : ℝ) : ℂ))
      ((t + rho : ℝ) : ℂ) :=
    (e.differentiableOn_invFun.differentiableAt
      (isOpen_rightHalfPlane rho |>.mem_nhds harg)).hasDerivAt
  have hinvR : HasDerivAt (fun y : ℝ ↦ e.invFun (y : ℂ))
      (deriv e.invFun ((t + rho : ℝ) : ℂ)) (t + rho) := hinv.comp_ofReal
  have hshift : HasDerivAt (fun x : ℝ ↦ x + rho) 1 t :=
    (hasDerivAt_id t).add_const rho
  have hcomp := hinvR.scomp t hshift
  convert hcomp using 1 <;> push_cast <;> simp [Function.comp_def]

/-- Lemma 2.1 gives the inverse-ray derivative estimate used in Corollary 2.3. -/
theorem norm_deriv_tractInverseRay_le {T : Set ℂ} {rho : ℝ} (e : TractEquiv T rho)
    (hexp : Set.InjOn Complex.exp T) {t : ℝ} (ht : 0 < t) :
    ‖deriv (tractInverseRay e) t‖ ≤ 2 / t := by
  let zeta := tractInverseRay e t
  have harg : (t : ℂ) + (rho : ℂ) ∈ rightHalfPlane rho := by
    simp only [rightHalfPlane, Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re]
    linarith
  have hzeta : zeta ∈ T := e.invFun_maps harg
  have hright : e.toFun zeta = (t : ℂ) + (rho : ℂ) := e.right_inv harg
  have hexpand := expansion_for_tract e hzeta hexp
  rw [hright] at hexpand
  simp only [Complex.add_re, Complex.ofReal_re] at hexpand
  have hprod := congrArg norm (e.deriv_mul_deriv_inv hzeta)
  simp only [norm_mul, norm_one] at hprod
  rw [hright] at hprod
  have hderiv := (hasDerivAt_tractInverseRay e ht).deriv
  rw [hderiv, le_div_iff₀ ht]
  have hnonneg : 0 ≤ ‖deriv e.invFun ((t : ℂ) + (rho : ℂ))‖ := norm_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hexpand hnonneg
  have hleft : t + rho - rho = t := by ring
  rw [hleft] at hmul
  calc
    ‖deriv e.invFun ((t : ℂ) + (rho : ℂ))‖ * t
        ≤ ‖deriv e.invFun ((t : ℂ) + (rho : ℂ))‖ *
            (2 * ‖deriv e.toFun zeta‖) := hmul
    _ = 2 * (‖deriv e.toFun zeta‖ *
          ‖deriv e.invFun ((t : ℂ) + (rho : ℂ))‖) := by ring
    _ = 2 := by rw [hprod, mul_one]

/-- Corollary 2.3 specialised to a tract equivalence.  The rightward-escape hypothesis is
the precise end condition used by the paper's intermediate-value argument. -/
theorem lower_order_for_tract
    {T : Set ℂ} {rho : ℝ} (e : TractEquiv T rho)
    (hexp : Set.InjOn Complex.exp T)
    (hescape : Tendsto (fun t ↦ (tractInverseRay e t).re) atTop atTop) :
    ∃ gamma > 0, ∃ sigma0 > 0, ∀ sigma ≥ sigma0,
      ∃ t, 1 ≤ t ∧ (tractInverseRay e t).re = sigma ∧
        sigma / 2 - gamma ≤ Real.log t := by
  apply lower_order_log_coordinate_of_re_escape
  · exact (continuousOn_tractInverseRay e).mono fun x hx ↦ by
      change 0 < x
      exact lt_of_lt_of_le zero_lt_one hx
  · intro x hx
    have hd := hasDerivAt_tractInverseRay e (lt_trans zero_lt_one hx)
    exact hd.congr_deriv hd.deriv.symm
  · intro x hx
    exact norm_deriv_tractInverseRay_le e hexp (lt_of_lt_of_le zero_lt_one hx)
  · exact hescape

/-- The challenge interface for Corollary 2.3, with the author-approved rightward end condition. -/
theorem lower_order_in_logarithmic_coordinates
    {T : Set ℂ} {ρ : ℝ} (e : TractEquiv T ρ)
    (hexp : Set.InjOn Complex.exp T)
    (hescape : Tendsto (fun t ↦ (tractInverseRay e t).re) atTop atTop) :
    ∃ γ > 0, ∃ σ₀ > 0, ∀ σ ≥ σ₀,
      ∃ t, 1 ≤ t ∧ (tractInverseRay e t).re = σ ∧
        σ / 2 - γ ≤ Real.log t :=
  lower_order_for_tract e hexp hescape

end

end EremenkoLyubichConstant
