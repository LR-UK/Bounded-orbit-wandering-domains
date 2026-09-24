/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

import EremenkoLyubichConstant.LogarithmicTransform
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.GroupTheory.SpecificGroups.Cyclic

open Function Set Complex
open scoped Topology

namespace EremenkoLyubichConstant

namespace ExteriorFundamentalGroup

/-- Integer deck translations of the exponential half-plane cover. -/
noncomputable instance deckAction (ρ : ℝ) : AddAction ℤ (rightHalfPlane ρ) where
  vadd n z := ⟨(z : ℂ) + (n : ℂ) * (2 * Real.pi * I), by
    simpa [rightHalfPlane] using z.2⟩
  zero_vadd z := by
    apply Subtype.ext
    change (z : ℂ) + ((0 : ℤ) : ℂ) * (2 * Real.pi * I) = (z : ℂ)
    simp
  add_vadd n m z := by
    apply Subtype.ext
    change (z : ℂ) + ((n + m : ℤ) : ℂ) * (2 * Real.pi * I) =
      ((z : ℂ) + (m : ℂ) * (2 * Real.pi * I)) + (n : ℂ) * (2 * Real.pi * I)
    push_cast
    ring

/-- The ambient formula for deck translations. -/
@[simp] theorem coe_deckAction {ρ : ℝ} (n : ℤ) (z : rightHalfPlane ρ) :
    ((n +ᵥ z : rightHalfPlane ρ) : ℂ) = (z : ℂ) + (n : ℂ) * (2 * Real.pi * I) := rfl

/-- Each integer deck translation is continuous on the half-plane. -/
instance (ρ : ℝ) : ContinuousConstVAdd ℤ (rightHalfPlane ρ) where
  continuous_const_vadd n := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.add continuous_const

/-- The integer deck action is free, and every deck translation is injective. -/
instance (ρ : ℝ) : IsCancelVAdd ℤ (rightHalfPlane ρ) where
  left_cancel' n z w h := by
    apply Subtype.ext
    exact add_right_cancel (congrArg Subtype.val h)
  right_cancel' n m z h := by
    have hc := congrArg Subtype.val h
    have hn : (n : ℂ) = (m : ℂ) :=
      mul_right_cancel₀ Complex.two_pi_I_ne_zero (add_left_cancel hc)
    exact_mod_cast hn

/-- The standard exponential cover of the exterior disk. -/
noncomputable def expCover (ρ : ℝ) (z : rightHalfPlane ρ) : exponentialExterior ρ :=
  ⟨Complex.exp z, by
    change Real.exp ρ < ‖Complex.exp (z : ℂ)‖
    rw [Complex.norm_exp]
    exact Real.exp_lt_exp.mpr z.2⟩

/-- The exponential half-plane cover is the quotient by integer deck translations. -/
theorem isAddQuotientCoveringMap_expCover (ρ : ℝ) :
    IsAddQuotientCoveringMap (expCover ρ) ℤ := by
  rw [isAddQuotientCoveringMap_iff_isCoveringMap_and]
  refine ⟨isCoveringMap_exp_rightHalfPlane ρ, ?_, inferInstance, inferInstance, ?_⟩
  · intro y
    have hn : (y : ℂ) ≠ 0 := norm_pos_iff.mp ((Real.exp_pos ρ).trans y.2)
    have hy : Complex.log y ∈ rightHalfPlane ρ := by
      change ρ < (Complex.log y).re
      rw [Complex.log_re, ← Real.exp_lt_exp, Real.exp_log (norm_pos_iff.mpr hn)]
      exact y.2
    exact ⟨⟨Complex.log y, hy⟩, Subtype.ext (Complex.exp_log hn)⟩
  · intro z w
    rw [Subtype.ext_iff]
    change Complex.exp (z : ℂ) = Complex.exp (w : ℂ) ↔ _
    rw [Complex.exp_eq_exp_iff_exists_int, AddAction.mem_orbit_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext hn.symm⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, (congrArg Subtype.val hn).symm⟩

/-- The fundamental group of any exterior disk is infinite cyclic. -/
noncomputable def fundamentalGroupEquivInt (ρ : ℝ) (z : rightHalfPlane ρ) :
    FundamentalGroup (exponentialExterior ρ) (expCover ρ z) ≃* Multiplicative ℤ := by
  letI : ContractibleSpace (rightHalfPlane ρ) :=
    (show Convex ℝ (rightHalfPlane ρ) from by
      simpa [rightHalfPlane] using convex_halfSpace_re_gt ρ).contractibleSpace
        ⟨(ρ + 1 : ℝ), by simp [rightHalfPlane]⟩
  exact ((isAddQuotientCoveringMap_expCover ρ).fundamentalGroupEquiv ⟨z, rfl⟩).trans
    MulOpposite.opMulEquiv.symm

/-- The integer of a loop records the endpoint of its exponential lift. -/
theorem fundamentalGroupEquivInt_eq_iff (ρ : ℝ) (z : rightHalfPlane ρ)
    (γ : FundamentalGroup (exponentialExterior ρ) (expCover ρ z)) (n : ℤ) :
    fundamentalGroupEquivInt ρ z γ = Multiplicative.ofAdd n ↔
      n +ᵥ z = ((isCoveringMap_exp_rightHalfPlane ρ).monodromy γ ⟨z, rfl⟩).1 := by
  change ((isAddQuotientCoveringMap_expCover ρ).fundamentalGroupToMulOpposite
    ⟨z, rfl⟩ γ).unop = (MulOpposite.op (Multiplicative.ofAdd n)).unop ↔ _
  rw [MulOpposite.unop_inj]
  exact (isAddQuotientCoveringMap_expCover ρ).fundamentalGroupToMulOpposite_apply_eq_Iff

/-- A lifted path computes the integer represented by a loop. -/
theorem fundamentalGroupEquivInt_eq_of_lift (ρ : ℝ) (z : rightHalfPlane ρ)
    (γ : FundamentalGroup (exponentialExterior ρ) (expCover ρ z)) (n : ℤ)
    (Γ : Path.Homotopic.Quotient z (n +ᵥ z))
    (he : expCover ρ (n +ᵥ z) = expCover ρ z)
    (hΓ : Γ.map ⟨expCover ρ, (isCoveringMap_exp_rightHalfPlane ρ).continuous⟩ =
      γ.toPath.cast rfl he) :
    fundamentalGroupEquivInt ρ z γ = Multiplicative.ofAdd n := by
  apply (fundamentalGroupEquivInt_eq_iff ρ z γ n).mpr
  exact congrArg Subtype.val
    ((isCoveringMap_exp_rightHalfPlane ρ).monodromy_eq_of_map_eq
      (ex := ⟨z, rfl⟩) (ey := ⟨n +ᵥ z, he⟩) Γ hΓ).symm

end ExteriorFundamentalGroup

/-- An open exterior covering with trivial fundamental-group image is a universal cover. -/
theorem exists_tractEquiv_of_trivial_covering_subgroup
    {T : Set ℂ} {ρ : ℝ} {f : ℂ → ℂ}
    (hT : IsOpen T) [PathConnectedSpace T]
    (hf : DifferentiableOn ℂ f T)
    (hmaps : MapsTo f T (exponentialExterior ρ))
    (hcover : IsCoveringMap fun z : T ↦
      (⟨f z, hmaps z.2⟩ : exponentialExterior ρ))
    (z₀ : T)
    (hπ : (FundamentalGroup.map ⟨fun z : T ↦
      (⟨f z, hmaps z.2⟩ : exponentialExterior ρ), hcover.continuous⟩ z₀).range = ⊥) :
    ∃ e : TractEquiv T ρ, ∀ z ∈ T, Complex.exp (e.toFun z) = f z := by
  let p : T → exponentialExterior ρ := fun z ↦ ⟨f z, hmaps z.2⟩
  let q := ExteriorFundamentalGroup.expCover ρ
  have hq : IsCoveringMap q := isCoveringMap_exp_rightHalfPlane ρ
  obtain ⟨w₀, hw₀⟩ := (ExteriorFundamentalGroup.isAddQuotientCoveringMap_expCover ρ).surjective (p z₀)
  let : LocallyPathConnectedSpace T := hT.locallyPathConnectedSpace
  let : ContractibleSpace (rightHalfPlane ρ) :=
    (show Convex ℝ (rightHalfPlane ρ) from by
      simpa [rightHalfPlane] using convex_halfSpace_re_gt ρ).contractibleSpace
        ⟨(ρ + 1 : ℝ), by simp [rightHalfPlane]⟩
  let : LocallyPathConnectedSpace (rightHalfPlane ρ) :=
    (isOpen_rightHalfPlane ρ).locallyPathConnectedSpace
  have hqπ : (FundamentalGroup.map ⟨q, hq.continuous⟩ w₀).range = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨a, rfl⟩ := hx
    rw [Subsingleton.elim a 1, map_one]
  obtain ⟨h, _, hcomm⟩ := exists_homeomorph_of_covering_subgroups hcover hq z₀ w₀ hw₀.symm
    (by rw [hπ]; exact bot_le)
    (by rw [hqπ]; exact bot_le)
  apply tractEquiv_of_homeomorph hT hf h
  intro z
  exact congrArg Subtype.val (congrFun hcomm z)

end EremenkoLyubichConstant
