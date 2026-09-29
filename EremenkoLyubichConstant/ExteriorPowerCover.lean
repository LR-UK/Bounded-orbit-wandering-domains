module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

public import EremenkoLyubichConstant.ExteriorFundamentalGroup
public import EremenkoLyubichConstant.CoveringNaturality

@[expose] public section

open Complex Set Function
open scoped Topology

namespace EremenkoLyubichConstant.ExteriorPowerCover

/-- Taking a positive power maps an exterior disk to an exterior disk. -/
theorem pow_mem_exterior_iff (ρ : ℝ) {d : ℕ} (hd : 0 < d) (z : ℂ) :
    z ^ d ∈ exponentialExterior ρ ↔ z ∈ exponentialExterior (ρ / d) := by
  have hpow : (Real.exp (ρ / d)) ^ d = Real.exp ρ := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  change Real.exp ρ < ‖z ^ d‖ ↔ Real.exp (ρ / d) < ‖z‖
  rw [norm_pow, ← hpow]
  exact pow_lt_pow_iff_left₀ (Real.exp_pos _).le (norm_nonneg _) hd.ne'

/-- The standard positive-degree power cover of an exterior disk. -/
def powerCover (ρ : ℝ) (d : ℕ) (hd : 0 < d)
    (z : exponentialExterior (ρ / d)) : exponentialExterior ρ :=
  ⟨(z : ℂ) ^ d, (pow_mem_exterior_iff ρ hd z).mpr z.2⟩

/-- Positive powers give covering maps of exterior disks. -/
theorem isCoveringMap_powerCover (ρ : ℝ) (d : ℕ) (hd : 0 < d) :
    IsCoveringMap (powerCover ρ d hd) := by
  have hsub : exponentialExterior ρ ⊆ ({0}ᶜ : Set ℂ) := by
    intro z hz
    exact norm_pos_iff.mp ((Real.exp_pos ρ).trans hz)
  have hc := ((isCoveringMapOn_npow d (show (d : ℂ) ≠ 0 by exact_mod_cast hd.ne')).mono
    hsub).isCoveringMap_restrictPreimage
  have heq : exponentialExterior (ρ / d) = (fun z : ℂ ↦ z ^ d) ⁻¹' exponentialExterior ρ := by
    ext z
    exact (pow_mem_exterior_iff ρ hd z).symm
  exact hc.comp_homeomorph (.setCongr heq)

/-- Multiplication by the degree lifts the standard power cover. -/
def scaleLift (ρ : ℝ) (d : ℕ) (hd : 0 < d)
    (z : rightHalfPlane (ρ / d)) : rightHalfPlane ρ :=
  ⟨(d : ℂ) * z, by
    change ρ < ((d : ℂ) * (z : ℂ)).re
    simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
    exact (div_lt_iff₀ (show (0 : ℝ) < d by exact_mod_cast hd)).mp z.2 |>.trans_eq (mul_comm _ _)⟩

/-- The exponential diagram for a power map commutes. -/
theorem exp_scaleLift (ρ : ℝ) (d : ℕ) (hd : 0 < d)
    (z : rightHalfPlane (ρ / d)) :
    ExteriorFundamentalGroup.expCover ρ (scaleLift ρ d hd z) =
      powerCover ρ d hd (ExteriorFundamentalGroup.expCover (ρ / d) z) := by
  apply Subtype.ext
  exact Complex.exp_nat_mul _ _

open ExteriorFundamentalGroup

set_option backward.isDefEq.respectTransparency false in
/-- On fundamental groups, a degree `d` power cover is multiplication by `d`. -/
theorem fundamentalGroup_powerCover (ρ : ℝ) (d : ℕ) (hd : 0 < d)
    (z : rightHalfPlane (ρ / d))
    (γ : FundamentalGroup (exponentialExterior (ρ / d)) (expCover (ρ / d) z)) :
    fundamentalGroupEquivInt ρ (scaleLift ρ d hd z)
        (FundamentalGroup.mapOfEq
          ⟨powerCover ρ d hd, (isCoveringMap_powerCover ρ d hd).continuous⟩
          (exp_scaleLift ρ d hd z).symm γ) =
      Multiplicative.ofAdd ((d : ℤ) * (fundamentalGroupEquivInt (ρ / d) z γ).toAdd) := by
  let L : C(rightHalfPlane (ρ / d), rightHalfPlane ρ) :=
    ⟨scaleLift ρ d hd, by
      apply Continuous.subtype_mk
      exact continuous_const.mul continuous_subtype_val⟩
  let q : C(exponentialExterior (ρ / d), exponentialExterior ρ) :=
    ⟨powerCover ρ d hd, (isCoveringMap_powerCover ρ d hd).continuous⟩
  have hc : (⟨expCover ρ, (isCoveringMap_exp_rightHalfPlane ρ).continuous⟩ :
      C(rightHalfPlane ρ, exponentialExterior ρ)).comp L =
      q.comp ⟨expCover (ρ / d), (isCoveringMap_exp_rightHalfPlane (ρ / d)).continuous⟩ := by
    ext w
    exact congrArg Subtype.val (exp_scaleLift ρ d hd w)
  apply (fundamentalGroupEquivInt_eq_iff _ _ _ _).mpr
  rw [FundamentalGroup.mapOfEq_apply, IsCoveringMap.monodromy_cast_val]
  refine Eq.trans ?_ ((isCoveringMap_exp_rightHalfPlane (ρ / d)).monodromy_naturality
    (isCoveringMap_exp_rightHalfPlane ρ) L q hc z γ).symm
  refine Eq.trans ?_ (congrArg L ((fundamentalGroupEquivInt_eq_iff (ρ / d) z γ
    (fundamentalGroupEquivInt (ρ / d) z γ).toAdd).mp rfl))
  apply Subtype.ext
  change (d : ℂ) * z + (((d : ℤ) * (fundamentalGroupEquivInt (ρ / d) z γ).toAdd : ℤ) : ℂ) *
    (2 * Real.pi * I) = (d : ℂ) * ((z : ℂ) +
      ((fundamentalGroupEquivInt (ρ / d) z γ).toAdd : ℂ) * (2 * Real.pi * I))
  push_cast
  ring

/-- The basepoint above a chosen half-plane point for a positive power cover. -/
noncomputable def divideLift (ρ : ℝ) (d : ℕ) (hd : 0 < d) (w : rightHalfPlane ρ) :
    rightHalfPlane (ρ / d) :=
  ⟨(w : ℂ) / d, by
    change ρ / d < ((w : ℂ) / (d : ℂ)).re
    rw [← Complex.ofReal_natCast, Complex.div_ofReal_re]
    exact (div_lt_div_iff_of_pos_right (show (0 : ℝ) < d by exact_mod_cast hd)).mpr w.2⟩

/-- Dividing by the degree is a right inverse of the lifted power map. -/
@[simp] theorem scale_divideLift (ρ : ℝ) (d : ℕ) (hd : 0 < d) (w : rightHalfPlane ρ) :
    scaleLift ρ d hd (divideLift ρ d hd w) = w := by
  apply Subtype.ext
  change (d : ℂ) * ((w : ℂ) / d) = w
  have hn : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

/-- The power-cover basepoint lies above the chosen exterior point. -/
theorem powerCover_basepoint (ρ : ℝ) (d : ℕ) (hd : 0 < d) (w : rightHalfPlane ρ) :
    powerCover ρ d hd (expCover (ρ / d) (divideLift ρ d hd w)) = expCover ρ w := by
  rw [← exp_scaleLift, scale_divideLift]

set_option backward.isDefEq.respectTransparency false in
/-- Membership in the power-cover subgroup is divisibility of the winding integer by the degree. -/
theorem mem_range_powerCover_iff (ρ : ℝ) (d : ℕ) (hd : 0 < d) (w : rightHalfPlane ρ)
    (γ : FundamentalGroup (exponentialExterior ρ) (expCover ρ w)) :
    γ ∈ (FundamentalGroup.mapOfEq
      ⟨powerCover ρ d hd, (isCoveringMap_powerCover ρ d hd).continuous⟩
      (powerCover_basepoint ρ d hd w)).range ↔
        (d : ℤ) ∣ (fundamentalGroupEquivInt ρ w γ).toAdd := by
  let e := fundamentalGroupEquivInt (ρ / d) (divideLift ρ d hd w)
  have hcalc (a : FundamentalGroup (exponentialExterior (ρ / d))
      (expCover (ρ / d) (divideLift ρ d hd w))) :
      fundamentalGroupEquivInt ρ w
        (FundamentalGroup.mapOfEq
          ⟨powerCover ρ d hd, (isCoveringMap_powerCover ρ d hd).continuous⟩
          (powerCover_basepoint ρ d hd w) a) =
        Multiplicative.ofAdd ((d : ℤ) * (e a).toAdd) := by
    have htransport (v : rightHalfPlane ρ)
        (hv : scaleLift ρ d hd (divideLift ρ d hd w) = v)
        (hb : powerCover ρ d hd (expCover (ρ / d) (divideLift ρ d hd w)) = expCover ρ v) :
        fundamentalGroupEquivInt ρ v
          (FundamentalGroup.mapOfEq
            ⟨powerCover ρ d hd, (isCoveringMap_powerCover ρ d hd).continuous⟩ hb a) =
          Multiplicative.ofAdd ((d : ℤ) * (e a).toAdd) := by
      subst v
      exact fundamentalGroup_powerCover ρ d hd (divideLift ρ d hd w) a
    exact htransport w (scale_divideLift ρ d hd w) (powerCover_basepoint ρ d hd w)
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(e a).toAdd, by rw [hcalc]; rfl⟩
  · rintro ⟨n, hn⟩
    refine ⟨e.symm (Multiplicative.ofAdd n), ?_⟩
    apply (fundamentalGroupEquivInt ρ w).injective
    rw [hcalc]
    rw [e.apply_symm_apply]
    exact congrArg Multiplicative.ofAdd hn.symm

end EremenkoLyubichConstant.ExteriorPowerCover
