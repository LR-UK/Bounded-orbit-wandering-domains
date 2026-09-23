/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li

Extracted unchanged from Dynamics/JuliaFatou/RepellingCycles.lean at
0a6497b0cc9ed39a6a705bf013449635894b56d0. The rational-dynamics imports are unnecessary here.
-/
import NoWanderingDomains.NormalFamilies.Spherical
import NoWanderingDomains.Sphere.MobiusAction
import Mathlib.Tactic
open OnePoint Polynomial Filter Topology Metric Function
namespace NoWanderingDomains

theorem sphericalDist_inversionGL_smul (x y : ℂ̂) :
    sphericalDist (inversionGL • x) (inversionGL • y) = sphericalDist x y := by
  have key : ∀ r : ℝ, 0 < r →
      Real.sqrt (1 + r⁻¹ ^ 2) = Real.sqrt (1 + r ^ 2) / r := by
    intro r hr
    have h1 : (1 + r⁻¹ ^ 2 : ℝ) = (1 + r ^ 2) / r ^ 2 := by
      field_simp
      ring
    rw [h1, Real.sqrt_div (by positivity) _, Real.sqrt_sq hr.le]
  have h0 : Real.sqrt (1 + ‖(0 : ℂ)‖ ^ 2) = 1 := by simp
  have hIC : ∀ c : ℂ, sphericalDist (∞ : ℂ̂) (c : ℂ̂) = chordalDistInfty c :=
    fun _ => rfl
  have hII : sphericalDist (∞ : ℂ̂) (∞ : ℂ̂) = 0 := rfl
  have hcc : ∀ a b : ℂ,
      sphericalDist (inversionGL • (a : ℂ̂)) (inversionGL • (b : ℂ̂)) =
        sphericalDist (a : ℂ̂) (b : ℂ̂) := by
    intro a b
    rw [inversionGL_smul_coe a, inversionGL_smul_coe b, sphericalDist_coe_coe]
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · subst ha; subst hb
      rw [if_pos rfl, hII]
      simp [chordalDist]
    · subst ha
      have hnb : (0 : ℝ) < ‖b‖ := norm_pos_iff.mpr hb
      have hsb : (0 : ℝ) < Real.sqrt (1 + ‖b‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
      rw [if_pos rfl, if_neg hb, hIC]
      simp only [chordalDistInfty, chordalDist, norm_inv, zero_sub, norm_neg]
      rw [key ‖b‖ hnb, h0, one_mul]
      field_simp
    · subst hb
      have hna : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha
      have hsa : (0 : ℝ) < Real.sqrt (1 + ‖a‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
      rw [if_neg ha, if_pos rfl, sphericalDist_coe_infty]
      simp only [chordalDistInfty, chordalDist, norm_inv, sub_zero]
      rw [key ‖a‖ hna, h0, mul_one]
      field_simp
    · have hna : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha
      have hnb : (0 : ℝ) < ‖b‖ := norm_pos_iff.mpr hb
      have hsa : (0 : ℝ) < Real.sqrt (1 + ‖a‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
      have hsb : (0 : ℝ) < Real.sqrt (1 + ‖b‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
      rw [if_neg ha, if_neg hb, sphericalDist_coe_coe]
      simp only [chordalDist, norm_inv]
      rw [inv_sub_inv ha hb, norm_div, norm_mul, norm_sub_rev b a,
        key ‖a‖ hna, key ‖b‖ hnb]
      field_simp
  have hci : ∀ a : ℂ,
      sphericalDist (inversionGL • (a : ℂ̂)) (inversionGL • (∞ : ℂ̂)) =
        sphericalDist (a : ℂ̂) (∞ : ℂ̂) := by
    intro a
    rw [inversionGL_smul_infty, inversionGL_smul_coe a, sphericalDist_coe_infty]
    by_cases ha : a = 0
    · subst ha
      rw [if_pos rfl]
      exact hIC 0
    · have hna : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha
      have hsa : (0 : ℝ) < Real.sqrt (1 + ‖a‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
      rw [if_neg ha, sphericalDist_coe_coe]
      simp only [chordalDist, chordalDistInfty, norm_inv, sub_zero]
      rw [key ‖a‖ hna, h0, mul_one]
      field_simp
  match x, y with
  | OnePoint.some a, OnePoint.some b => exact hcc a b
  | OnePoint.some a, ∞ => exact hci a
  | ∞, OnePoint.some b =>
      rw [sphericalDist_comm (inversionGL • (∞ : ℂ̂)), sphericalDist_comm (∞ : ℂ̂)]
      exact hci b
  | ∞, ∞ =>
      rw [inversionGL_smul_infty, hII, sphericalDist_coe_coe]
      simp [chordalDist]


end NoWanderingDomains
