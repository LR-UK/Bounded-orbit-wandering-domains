module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

public import EremenkoLyubichConstant.ClassB
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Meromorphic.Basic

@[expose] public section

open Filter Metric Set Polynomial
open scoped Topology

namespace FunctionTheory

/-- Polynomiality is unchanged by an invertible affine change of source coordinate. -/
theorem isPolynomialFunction_of_affine_precomp
    {f : ℂ → ℂ} {c a : ℂ} (hc : c ≠ 0)
    (hp : IsPolynomialFunction (fun z ↦ f (c * z + a))) : IsPolynomialFunction f := by
  obtain ⟨p, hp⟩ := hp
  refine ⟨p.comp (Polynomial.C c⁻¹ * (Polynomial.X - Polynomial.C a)), funext fun z ↦ ?_⟩
  have hh := congrFun hp ((z - a) / c)
  have harg : c * ((z - a) / c) + a = z := by field_simp; ring
  rw [harg] at hh
  simpa [Polynomial.eval_comp, div_eq_mul_inv, mul_comm] using hh

/-- An entire function with a polynomial bound outside a disk is a polynomial. -/
theorem isPolynomialFunction_of_polynomial_growth
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C R : ℝ} {m : ℕ}
    (hb : ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ m) :
    IsPolynomialFunction f := by
  have hz (n : ℕ) (hn : m < n) : iteratedDeriv n f 0 = 0 := by
    have hlim : Tendsto (fun r : ℝ ↦ (n.factorial : ℝ) * C * (r ^ m / r ^ n))
        atTop (𝓝 0) := by
      simpa using (tendsto_pow_div_pow_atTop_zero hn).const_mul ((n.factorial : ℝ) * C)
    have hbound : ∀ᶠ r : ℝ in atTop,
        ‖iteratedDeriv n f 0‖ ≤ (n.factorial : ℝ) * C * (r ^ m / r ^ n) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop R] with r hr hR
      have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0) n hr
        hf.diffContOnCl (C := C * r ^ m) (fun z hz ↦ by
          have hnz : ‖z‖ = r := by simpa [mem_sphere_iff_norm] using hz
          simpa [hnz] using hb z (hnz.symm ▸ hR))
      convert h using 1; ring
    exact norm_le_zero_iff.mp (ge_of_tendsto hlim hbound)
  let p : ℂ[X] := ∑ n ∈ Finset.range (m + 1),
    Polynomial.monomial n ((n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0)
  refine ⟨p, funext fun z ↦ ?_⟩
  rw [← Complex.taylorSeries_eq_of_entire' 0 z hf]
  rw [tsum_eq_sum (s := Finset.range (m + 1))]
  · simp [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  · intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    simp [hz n (by omega)]

/-- Meromorphy at infinity of an entire function forces polynomiality. -/
theorem isPolynomialFunction_of_meromorphicAt_infinity
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hm : MeromorphicAt (fun z : ℂ ↦ f z⁻¹) 0) : IsPolynomialFunction f := by
  obtain ⟨m, hm⟩ := hm
  have hcont := hm.continuousAt.norm
  have hb : ∀ᶠ z in 𝓝 (0 : ℂ), ‖(z - 0) ^ m • f z⁻¹‖ <
      ‖(0 - 0 : ℂ) ^ m • f (0 : ℂ)⁻¹‖ + 1 :=
    hcont.eventually (gt_mem_nhds (by linarith))
  obtain ⟨ε, hε, hbound⟩ := Metric.eventually_nhds_iff.mp hb
  apply isPolynomialFunction_of_polynomial_growth hf (R := max 1 (2 / ε))
    (m := m) (C := ‖(0 - 0 : ℂ) ^ m • f (0 : ℂ)⁻¹‖ + 1)
  intro z hz
  have hnorm : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hz)
  have hlarge : 2 / ε ≤ ‖z‖ := (le_max_right _ _).trans hz
  have hsmall : dist z⁻¹ 0 < ε := by
    rw [dist_zero_right, norm_inv, inv_eq_one_div, div_lt_iff₀ hnorm]
    have := (div_le_iff₀ hε).mp hlarge
    nlinarith
  have h := (hbound hsmall).le
  simp only [sub_zero, norm_smul, norm_pow, norm_inv, inv_inv, inv_pow] at h
  simpa only [sub_zero, norm_smul, norm_pow, mul_comm] using
    (inv_mul_le_iff₀ (pow_pos hnorm m)).mp h

/-- A transcendental entire function has values of arbitrarily small modulus. -/
theorem IsTranscendentalEntire.exists_norm_lt {f : ℂ → ℂ}
    (hf : IsTranscendentalEntire f) {R : ℝ} (hR : 0 < R) :
    ∃ z : ℂ, ‖f z‖ < R := by
  by_contra hn
  push Not at hn
  have hne (z : ℂ) : f z ≠ 0 := norm_pos_iff.mp (hR.trans_le (hn z))
  have hi : Differentiable ℂ (fun z ↦ (f z)⁻¹) := hf.1.inv hne
  have hb : Bornology.IsBounded (range fun z ↦ (f z)⁻¹) := by
    apply (isBounded_closedBall (x := (0 : ℂ)) (r := R⁻¹)).subset
    rintro _ ⟨z, rfl⟩
    rw [mem_closedBall_zero_iff, norm_inv]
    exact (inv_le_inv₀ (hR.trans_le (hn z)) hR).mpr (hn z)
  apply hf.2
  refine ⟨Polynomial.C (f 0), funext fun z ↦ ?_⟩
  simpa using inv_injective (hi.apply_eq_apply_of_bounded hb z 0)

/-- Every exterior preimage of a transcendental entire function omits a nonempty disk. -/
theorem IsTranscendentalEntire.exterior_omits_ball {f : ℂ → ℂ}
    (hf : IsTranscendentalEntire f) {R : ℝ} (hR : 0 < R) :
    ∃ b : ℂ, ∃ ε > 0, ∀ z, R < ‖f z‖ → ε ≤ ‖z - b‖ := by
  obtain ⟨b, hb⟩ := hf.exists_norm_lt hR
  have ho : IsOpen {z : ℂ | ‖f z‖ < R} := isOpen_lt hf.1.continuous.norm continuous_const
  obtain ⟨ε, hε, he⟩ := Metric.isOpen_iff.mp ho b hb
  refine ⟨b, ε, hε, fun z hz ↦ ?_⟩
  by_contra hn
  have hh : ‖f z‖ < R := he (by simpa only [mem_ball, dist_eq_norm] using lt_of_not_ge hn)
  exact (not_lt_of_ge hh.le) hz

end FunctionTheory
