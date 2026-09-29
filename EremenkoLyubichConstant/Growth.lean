module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

public import EremenkoLyubichConstant.Consequences
public import Mathlib.Topology.MetricSpace.ProperSpace

@[expose] public section

/-! # Maximum modulus and growth consequences -/

open Set Metric Filter Topology

namespace EremenkoLyubichConstant

noncomputable section

/-- Maximum modulus on the circle of radius `r`, using Mathlib's supremum. -/
def maximumModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup (norm ∘ f '' sphere (0 : ℂ) r)

/-- Every value on the circle is bounded by the maximum modulus. -/
theorem norm_le_maximumModulus {f : ℂ → ℂ} (hf : Continuous f)
    {z : ℂ} : ‖f z‖ ≤ maximumModulus f ‖z‖ := by
  apply le_csSup
  · exact (isCompact_sphere (0 : ℂ) ‖z‖).bddAbove_image
      ((continuous_norm.comp hf).continuousOn)
  · refine ⟨z, ?_, rfl⟩
    simp

/-- For a genuine logarithmic transform of an entire function, the inverse positive ray
escapes to the right.  This is stronger than merely escaping compact subsets of the
logarithmic plane. -/
theorem tendsto_tractInverseRay_re_atTop
    {T : Set ℂ} {rho : ℝ} (e : TractEquiv T rho) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hfun : ∀ z ∈ T, Complex.exp (e.toFun z) = f (Complex.exp z)) :
    Tendsto (fun t ↦ (tractInverseRay e t).re) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro b
  have hcompact : IsCompact (closedBall (0 : ℂ) (Real.exp b)) :=
    isCompact_closedBall (0 : ℂ) (Real.exp b)
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (hcompact.bddAbove_image ((continuous_norm.comp hf.continuous).continuousOn))
  have hexp : Tendsto (fun t : ℝ ↦ Real.exp (t + rho)) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (tendsto_atTop_add_const_right atTop rho tendsto_id)
  filter_upwards [hexp (eventually_gt_atTop C), eventually_gt_atTop (0 : ℝ)] with t htC ht
  change C < Real.exp (t + rho) at htC
  by_contra hnot
  have hre : (tractInverseRay e t).re < b := lt_of_not_ge hnot
  have harg : (t : ℂ) + (rho : ℂ) ∈ rightHalfPlane rho := by
    simp only [rightHalfPlane, Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re]
    linarith
  have hz : tractInverseRay e t ∈ T := e.invFun_maps harg
  have hto : e.toFun (tractInverseRay e t) = (t : ℂ) + (rho : ℂ) :=
    e.right_inv harg
  have hwball : Complex.exp (tractInverseRay e t) ∈
      closedBall (0 : ℂ) (Real.exp b) := by
    rw [mem_closedBall_zero_iff, Complex.norm_exp]
    exact (Real.exp_lt_exp.mpr hre).le
  have hupper : ‖f (Complex.exp (tractInverseRay e t))‖ ≤ C :=
    hC _ ⟨Complex.exp (tractInverseRay e t), hwball, rfl⟩
  have hvalue : ‖f (Complex.exp (tractInverseRay e t))‖ = Real.exp (t + rho) := by
    rw [← hfun _ hz, Complex.norm_exp, hto]
    simp only [Complex.add_re, Complex.ofReal_re]
  linarith

/-- The maximum-modulus lower bound obtained from a single logarithmic tract. -/
theorem lower_order_of_logarithmic_tract
    {T : Set ℂ} {rho : ℝ} (e : TractEquiv T rho) {f : ℂ → ℂ}
    (hrho : 0 ≤ rho) (hexp : Set.InjOn Complex.exp T)
    (hf : Differentiable ℂ f)
    (hfun : ∀ z ∈ T, Complex.exp (e.toFun z) = f (Complex.exp z)) :
    ∃ c > 0, ∃ r0 > 1, ∀ r ≥ r0,
      c * Real.sqrt r ≤ Real.log (maximumModulus f r) := by
  obtain ⟨gamma, hgamma, sigma0, hsigma0, hgrowth⟩ :=
    lower_order_for_tract e hexp (tendsto_tractInverseRay_re_atTop e hf hfun)
  let c := Real.exp (-gamma)
  let r0 := Real.exp (max sigma0 1)
  have hc : 0 < c := Real.exp_pos _
  have hr0 : 1 < r0 := by
    rw [show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  refine ⟨c, hc, r0, hr0, ?_⟩
  intro r hr
  have hrpos : 0 < r := lt_trans zero_lt_one (hr0.trans_le hr)
  have hsigma : sigma0 ≤ Real.log r := by
    have hlogr0 : max sigma0 1 ≤ Real.log r := by
      rw [← Real.exp_le_exp]
      simpa [r0, Real.exp_log hrpos] using hr
    exact (le_max_left _ _).trans hlogr0
  obtain ⟨t, ht, hre, hlogt⟩ := hgrowth (Real.log r) hsigma
  let z := tractInverseRay e t
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have harg : (t : ℂ) + (rho : ℂ) ∈ rightHalfPlane rho := by
    simp only [rightHalfPlane, Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re]
    linarith
  have hz : z ∈ T := e.invFun_maps harg
  have hto : e.toFun z = (t : ℂ) + (rho : ℂ) := e.right_inv harg
  have hnormz : ‖Complex.exp z‖ = r := by
    rw [Complex.norm_exp, show z.re = Real.log r from hre, Real.exp_log hrpos]
  have hvalue : ‖f (Complex.exp z)‖ = Real.exp (t + rho) := by
    rw [← hfun z hz, Complex.norm_exp, hto]
    simp only [Complex.add_re, Complex.ofReal_re]
  have hmax : Real.exp (t + rho) ≤ maximumModulus f r := by
    rw [← hvalue, ← hnormz]
    exact norm_le_maximumModulus hf.continuous
  have hmaxpos : 0 < maximumModulus f r := (Real.exp_pos _).trans_le hmax
  have hlogmax : t + rho ≤ Real.log (maximumModulus f r) := by
    rw [← Real.log_exp (t + rho)]
    exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos _) hmaxpos hmax
  have hexpbound : Real.exp (Real.log r / 2 - gamma) ≤ t := by
    rw [← Real.exp_log htpos]
    exact Real.exp_le_exp.mpr hlogt
  have hsqrt : Real.sqrt r = Real.exp (Real.log r / 2) := by
    rw [Real.sqrt_eq_iff_eq_sq hrpos.le (Real.exp_pos _).le,
      pow_two, ← Real.exp_add, add_halves, Real.exp_log hrpos]
  calc
    c * Real.sqrt r = Real.exp (Real.log r / 2 - gamma) := by
      change Real.exp (-gamma) * Real.sqrt r = _
      rw [hsqrt, ← Real.exp_add]
      congr 1
      ring
    _ ≤ t := hexpbound
    _ ≤ t + rho := by linarith
    _ ≤ Real.log (maximumModulus f r) := hlogmax

end

end EremenkoLyubichConstant
