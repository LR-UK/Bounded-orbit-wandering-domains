module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

public import EremenkoLyubichConstant.Mobius
public import EremenkoLyubichConstant.Expansion

@[expose] public section

/-!
# Constructing the auxiliary Koebe map

This file formalises the explicit construction in Lemma 2.1 of
Lasse Rempe, *The Eremenko--Lyubich constant*.
-/

open Set Metric Filter
open scoped Topology

namespace EremenkoLyubichConstant

noncomputable section

/-- A right half-plane is open. -/
lemma isOpen_rightHalfPlane (ρ : ℝ) : IsOpen (rightHalfPlane ρ) :=
  isOpen_lt continuous_const Complex.continuous_re

/-- A conformal equivalence between a plane domain and a right half-plane, represented
by mutually inverse ambient maps. -/
structure TractEquiv (T : Set ℂ) (ρ : ℝ) where
  /-- Forward conformal chart, extended to the plane. -/
  toFun : ℂ → ℂ
  /-- Inverse conformal chart, extended to the plane. -/
  invFun : ℂ → ℂ
  /-- The tract is open. -/
  isOpen_source : IsOpen T
  /-- The forward chart maps the tract to the half-plane. -/
  toFun_maps : MapsTo toFun T (rightHalfPlane ρ)
  /-- The inverse chart maps the half-plane to the tract. -/
  invFun_maps : MapsTo invFun (rightHalfPlane ρ) T
  /-- The inverse is a left inverse on the tract. -/
  left_inv : Set.LeftInvOn invFun toFun T
  /-- The inverse is a right inverse on the half-plane. -/
  right_inv : Set.RightInvOn invFun toFun (rightHalfPlane ρ)
  /-- The forward chart is complex differentiable on the tract. -/
  differentiableOn_toFun : DifferentiableOn ℂ toFun T
  /-- The inverse chart is complex differentiable on the half-plane. -/
  differentiableOn_invFun : DifferentiableOn ℂ invFun (rightHalfPlane ρ)

/-- The affine rescaling of the disc-to-half-plane map used at `ζ`. -/
def centredHalfPlaneMap (phi : ℂ → ℂ) (ρ : ℝ) (ζ z : ℂ) : ℂ :=
  (((phi ζ).re - ρ : ℝ) : ℂ) * discToRight z +
    ((ρ : ℂ) + ((phi ζ).im : ℂ) * Complex.I)

/-- The centred half-plane map sends zero to the chosen chart value. -/
lemma centredHalfPlaneMap_zero {phi : ℂ → ℂ} {ρ : ℝ} {ζ : ℂ} :
    centredHalfPlaneMap phi ρ ζ 0 = phi ζ := by
  apply Complex.ext <;> simp [centredHalfPlaneMap, discToRight]

/-- The centred map sends the unit disc into the target half-plane. -/
lemma centredHalfPlaneMap_mem {phi : ℂ → ℂ} {ρ : ℝ} {ζ z : ℂ}
    (hphi : ρ < (phi ζ).re) (hz : z ∈ unitDisc) :
    centredHalfPlaneMap phi ρ ζ z ∈ rightHalfPlane ρ := by
  simp only [centredHalfPlaneMap, rightHalfPlane, Set.mem_ofPred_eq, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.I_re, Complex.I_im, mul_zero, add_zero]
  have hM := discToRight_maps z hz
  nlinarith

/-- Derivative of the centred half-plane map at zero. -/
lemma hasDerivAt_centredHalfPlaneMap_zero {phi : ℂ → ℂ} {ρ : ℝ} {ζ : ℂ} :
    HasDerivAt (centredHalfPlaneMap phi ρ ζ)
      (-2 * (((phi ζ).re - ρ : ℝ) : ℂ)) 0 := by
  have h := hasDerivAt_discToRight_zero.const_mul
    ((((phi ζ).re - ρ : ℝ) : ℂ)) |>.add_const
      ((ρ : ℂ) + ((phi ζ).im : ℂ) * Complex.I)
  convert h using 1
  · funext z
    simp [centredHalfPlaneMap]
  · ring

/-- The centred half-plane map is differentiable at points of the unit disc. -/
lemma differentiableAt_centredHalfPlaneMap {phi : ℂ → ℂ} {ρ : ℝ} {ζ z : ℂ}
    (hz : z ∈ unitDisc) : DifferentiableAt ℂ (centredHalfPlaneMap phi ρ ζ) z := by
  have hne := one_add_ne_zero_of_mem_unitDisc hz
  unfold centredHalfPlaneMap discToRight
  fun_prop

/-- The derivative of the inverse chart is reciprocal to that of the forward chart. -/
lemma TractEquiv.deriv_mul_deriv_inv
    {T : Set ℂ} {ρ : ℝ} (e : TractEquiv T ρ) {ζ : ℂ} (hζ : ζ ∈ T) :
    deriv e.toFun ζ * deriv e.invFun (e.toFun ζ) = 1 := by
  have hw : e.toFun ζ ∈ rightHalfPlane ρ := e.toFun_maps hζ
  have hto : DifferentiableAt ℂ e.toFun ζ :=
    e.differentiableOn_toFun.differentiableAt (e.isOpen_source.mem_nhds hζ)
  have hinv : DifferentiableAt ℂ e.invFun (e.toFun ζ) :=
    e.differentiableOn_invFun.differentiableAt (isOpen_rightHalfPlane ρ |>.mem_nhds hw)
  have hcomp : HasDerivAt (e.toFun ∘ e.invFun)
      (deriv e.toFun ζ * deriv e.invFun (e.toFun ζ)) (e.toFun ζ) := by
    have hto' : HasDerivAt e.toFun (deriv e.toFun ζ) (e.invFun (e.toFun ζ)) := by
      simpa [e.left_inv hζ] using hto.hasDerivAt
    exact hto'.comp (e.toFun ζ) hinv.hasDerivAt
  have hevent : (e.toFun ∘ e.invFun) =ᶠ[nhds (e.toFun ζ)] id := by
    filter_upwards [isOpen_rightHalfPlane ρ |>.eventually_mem hw] with w hw
    exact e.right_inv hw
  exact hcomp.unique ((hasDerivAt_id (𝕜 := ℂ) (e.toFun ζ)).congr_of_eventuallyEq hevent)

/-- The auxiliary univalent function from the proof of Lemma 2.1. -/
def tractKoebeMap {T : Set ℂ} {ρ : ℝ} (e : TractEquiv T ρ) (ζ z : ℂ) : ℂ :=
  Complex.exp (e.invFun (centredHalfPlaneMap e.toFun ρ ζ z) - ζ)

/-- The auxiliary Koebe map is normalised to take value one at zero. -/
lemma tractKoebeMap_zero {T : Set ℂ} {ρ : ℝ} (e : TractEquiv T ρ)
    {ζ : ℂ} (hζ : ζ ∈ T) : tractKoebeMap e ζ 0 = 1 := by
  simp [tractKoebeMap, centredHalfPlaneMap_zero, e.left_inv hζ]

/-- The auxiliary exponential lift omits zero. -/
lemma tractKoebeMap_omits_zero {T : Set ℂ} {ρ : ℝ} (e : TractEquiv T ρ) (ζ : ℂ) :
    (0 : ℂ) ∉ tractKoebeMap e ζ '' unitDisc := by
  rintro ⟨z, -, hz⟩
  exact Complex.exp_ne_zero _ hz

/-- The auxiliary Koebe map is complex differentiable on the unit disc. -/
lemma tractKoebeMap_differentiableOn {T : Set ℂ} {ρ : ℝ} (e : TractEquiv T ρ)
    {ζ : ℂ} (hζ : ζ ∈ T) : DifferentiableOn ℂ (tractKoebeMap e ζ) unitDisc := by
  intro z hz
  have hw := centredHalfPlaneMap_mem (e.toFun_maps hζ) hz
  have hA := differentiableAt_centredHalfPlaneMap (phi := e.toFun) (ρ := ρ) (ζ := ζ) hz
  have hi := e.differentiableOn_invFun.differentiableAt
    (isOpen_rightHalfPlane ρ |>.mem_nhds hw)
  exact (Complex.differentiableAt_exp.comp z ((hi.comp z hA).sub_const ζ)).differentiableWithinAt

/-- The centred half-plane map is injective on the unit disc. -/
lemma centredHalfPlaneMap_injOn {phi : ℂ → ℂ} {ρ : ℝ} {ζ : ℂ}
    (hpos : ρ < (phi ζ).re) : Set.InjOn (centredHalfPlaneMap phi ρ ζ) unitDisc := by
  intro x hx y hy hxy
  have ha : ((((phi ζ).re - ρ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt (sub_pos.mpr hpos)
  apply discToRight_injective hx hy
  apply (mul_left_cancel₀ ha)
  simpa only [centredHalfPlaneMap, add_left_inj] using hxy

/-- Injectivity of the exponential on the tract makes the auxiliary map univalent. -/
lemma tractKoebeMap_injOn {T : Set ℂ} {ρ : ℝ} (e : TractEquiv T ρ)
    {ζ : ℂ} (hζ : ζ ∈ T) (hexp : Set.InjOn Complex.exp T) :
    Set.InjOn (tractKoebeMap e ζ) unitDisc := by
  intro x hx y hy hxy
  have hAx := centredHalfPlaneMap_mem (e.toFun_maps hζ) hx
  have hAy := centredHalfPlaneMap_mem (e.toFun_maps hζ) hy
  have hix := e.invFun_maps hAx
  have hiy := e.invFun_maps hAy
  simp only [tractKoebeMap] at hxy
  have heq : e.invFun (centredHalfPlaneMap e.toFun ρ ζ x) =
      e.invFun (centredHalfPlaneMap e.toFun ρ ζ y) := by
    apply hexp hix hiy
    calc
      Complex.exp (e.invFun (centredHalfPlaneMap e.toFun ρ ζ x)) =
          Complex.exp (e.invFun (centredHalfPlaneMap e.toFun ρ ζ x) - ζ) *
            Complex.exp ζ := by rw [← Complex.exp_add]; congr 1; ring
      _ = Complex.exp (e.invFun (centredHalfPlaneMap e.toFun ρ ζ y) - ζ) *
            Complex.exp ζ := by rw [hxy]
      _ = Complex.exp (e.invFun (centredHalfPlaneMap e.toFun ρ ζ y)) := by
        rw [← Complex.exp_add]; congr 1; ring
  have hA : centredHalfPlaneMap e.toFun ρ ζ x =
      centredHalfPlaneMap e.toFun ρ ζ y := by
    rw [← e.right_inv hAx, ← e.right_inv hAy, heq]
  exact centredHalfPlaneMap_injOn (e.toFun_maps hζ) hx hy hA

/-- Lemma 2.1 of the paper, now with the auxiliary Koebe map constructed from the
stated tract equivalence and injectivity of the exponential on the tract. -/
theorem expansion_for_tract
    {T : Set ℂ} {ρ : ℝ} (e : TractEquiv T ρ) {ζ : ℂ}
    (hζ : ζ ∈ T) (hexp : Set.InjOn Complex.exp T) :
    (e.toFun ζ).re - ρ ≤ 2 * ‖deriv e.toFun ζ‖ := by
  have hw := e.toFun_maps hζ
  have hA := hasDerivAt_centredHalfPlaneMap_zero
    (phi := e.toFun) (ρ := ρ) (ζ := ζ)
  have hi : DifferentiableAt ℂ e.invFun (e.toFun ζ) :=
    e.differentiableOn_invFun.differentiableAt
      (isOpen_rightHalfPlane ρ |>.mem_nhds hw)
  have hinner : HasDerivAt
      (fun z => e.invFun (centredHalfPlaneMap e.toFun ρ ζ z) - ζ)
      (deriv e.invFun (e.toFun ζ) * (-2 * (((e.toFun ζ).re - ρ : ℝ) : ℂ))) 0 := by
    convert (hi.hasDerivAt.comp_of_eq 0 hA centredHalfPlaneMap_zero.symm).sub_const ζ using 1
    · funext z
      rfl
  have hgder : HasDerivAt (tractKoebeMap e ζ)
      (deriv e.invFun (e.toFun ζ) * (-2 * (((e.toFun ζ).re - ρ : ℝ) : ℂ))) 0 := by
    have hc := (Complex.hasDerivAt_exp 0).comp_of_eq 0 hinner (by
      rw [centredHalfPlaneMap_zero, e.left_inv hζ]
      ring)
    convert hc using 1
    · funext z
      rfl
    · simp
  have hK : ‖deriv (tractKoebeMap e ζ) 0‖ ≤ 4 :=
    norm_deriv_le_four_of_eq_one_omits_zero
      (tractKoebeMap_differentiableOn e hζ)
      (tractKoebeMap_injOn e hζ hexp)
      (tractKoebeMap_zero e hζ)
      (tractKoebeMap_omits_zero e ζ)
  rw [hgder.deriv, norm_mul] at hK
  have ha : 0 < (e.toFun ζ).re - ρ := sub_pos.mpr hw
  have hnormreal : ‖((((e.toFun ζ).re - ρ : ℝ) : ℂ))‖ =
      (e.toFun ζ).re - ρ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hscale : ‖(-2 : ℂ) * (((e.toFun ζ).re - ρ : ℝ) : ℂ)‖ =
      2 * ((e.toFun ζ).re - ρ) := by
    rw [norm_mul, hnormreal]
    norm_num
  rw [hscale] at hK
  have hinv := e.deriv_mul_deriv_inv hζ
  have hinvNorm := congrArg norm hinv
  simp only [norm_mul, norm_one] at hinvNorm
  have hto_nonneg : 0 ≤ ‖deriv e.toFun ζ‖ := norm_nonneg _
  have hi_nonneg : 0 ≤ ‖deriv e.invFun (e.toFun ζ)‖ := norm_nonneg _
  nlinarith

/-- Theorem 1.1, inequality (1.4), for a logarithmic transform satisfying
`exp ∘ F = f ∘ exp`. -/
theorem expansion_for_logarithmic_transform
    {T : Set ℂ} {ρ : ℝ} (e : TractEquiv T ρ) {f : ℂ → ℂ} {ζ : ℂ}
    (hζ : ζ ∈ T) (hexp : Set.InjOn Complex.exp T)
    (hfun : ∀ z ∈ T, Complex.exp (e.toFun z) = f (Complex.exp z))
    (hf : DifferentiableAt ℂ f (Complex.exp ζ)) :
    (((e.toFun ζ).re - ρ) * ‖Complex.exp (e.toFun ζ)‖) / 2 ≤
      ‖deriv f (Complex.exp ζ)‖ * ‖Complex.exp ζ‖ := by
  have hto : DifferentiableAt ℂ e.toFun ζ :=
    e.differentiableOn_toFun.differentiableAt (e.isOpen_source.mem_nhds hζ)
  have hid := logarithmic_derivative_norm_identity_of_eventuallyEq
    ((e.isOpen_source.eventually_mem hζ).mono fun z hz ↦ hfun z hz) hto hf
  apply expansion_in_original_coordinates _ hid
  have hmain := expansion_for_tract e hζ hexp
  nlinarith

end

end EremenkoLyubichConstant
