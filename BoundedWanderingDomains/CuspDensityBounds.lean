/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.DiscCoveringMetric
import FunctionTheory.Conformal.SchottkyDisc
import Mathlib.Analysis.Complex.BorelCaratheodory

open Set Metric Function

namespace AreaDeficit

/-- A non-optimal Carathéodory derivative estimate, sufficient for cusp bounds. -/
theorem norm_deriv_le_of_re_upper {f : ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hM : (f 0).re < M) (hb : ∀ z ∈ ball 0 R, (f z).re ≤ M) :
    ‖deriv f 0‖ ≤ 4 * (M - (f 0).re) / R := by
  let g : ℂ → ℂ := fun z => f z - f 0
  have hg : DifferentiableOn ℂ g (ball 0 R) := hf.sub_const _
  have hg0 : g 0 = 0 := sub_self _
  have hhalf : 0 < R / 2 := by positivity
  have hmap : MapsTo g (ball 0 (R / 2)) (closedBall (g 0) (2 * (M - (f 0).re))) := by
    intro z hz
    have hzn : ‖z‖ < R / 2 := mem_ball_zero_iff.mp hz
    have hzR : z ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (by linarith)
    have he := Complex.borelCaratheodory_zero (sub_pos.mpr hM) hg
      (fun w hw => by change (f w - f 0).re ≤ M - (f 0).re; simp only [Complex.sub_re]; linarith [hb w hw])
      hR hzR hg0
    rw [hg0, mem_closedBall_zero_iff]
    apply he.trans
    apply (div_le_iff₀ (by linarith : 0 < R - ‖z‖)).mpr
    nlinarith
  have hd := Complex.norm_deriv_le_div_of_mapsTo_ball
    (hg.mono (ball_subset_ball (by linarith : R / 2 ≤ R))) hmap hhalf
  have he : deriv g 0 = deriv f 0 := by dsimp [g]; rw [deriv_sub_const]
  rw [he] at hd
  convert hd using 1
  ring

/-- Logarithmic derivative bound for a bounded zero-free function on a disc.
The extra constant 1 avoids a separate equality case. -/
theorem norm_deriv_le_of_zero_free_bounded {f : ℂ → ℂ} {R B : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hzero : ∀ z ∈ ball 0 R, f z ≠ 0)
    (hbound : ∀ z ∈ ball 0 R, ‖f z‖ ≤ B) :
    ‖deriv f 0‖ ≤ 4 * ‖f 0‖ * (1 + Real.log B - Real.log ‖f 0‖) / R := by
  have h0 : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hsc : IsSimplyConnected (ball (0 : ℂ) R) := by
    let : ContractibleSpace (ball (0 : ℂ) R) :=
      (convex_ball (0 : ℂ) R).contractibleSpace ⟨0, h0⟩
    change SimplyConnectedSpace (ball (0 : ℂ) R)
    infer_instance
  obtain ⟨L, hL, he⟩ := TauCeti.exists_differentiableOn_eqOn_exp_comp hsc isOpen_ball hf
    (by rintro ⟨z, hz, hez⟩; exact hzero z hz hez)
  have hlog : ∀ z ∈ ball 0 R, (L z).re = Real.log ‖f z‖ := by
    intro z hz
    rw [← he hz, Function.comp_apply, Complex.norm_exp, Real.log_exp]
  have hlogle : ∀ z ∈ ball 0 R, (L z).re ≤ Real.log B := by
    intro z hz
    rw [hlog z hz]
    exact Real.log_le_log (norm_pos_iff.mpr (hzero z hz)) (hbound z hz)
  have hd := norm_deriv_le_of_re_upper hR hL
    (M := 1 + Real.log B) (by linarith [hlogle 0 h0])
    (fun z hz => by linarith [hlogle z hz])
  have hder : deriv f 0 = Complex.exp (L 0) * deriv L 0 := by
    have hLd := hL.differentiableAt (isOpen_ball.mem_nhds h0)
    have hevent : (fun z => Complex.exp (L z)) =ᶠ[nhds 0] f :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds h0) (fun z hz => he hz)
    exact hevent.deriv_eq.symm.trans hLd.hasDerivAt.cexp.deriv
  rw [hder, norm_mul, show Complex.exp (L 0) = f 0 from he h0]
  have hd' := mul_le_mul_of_nonneg_left hd (norm_nonneg (f 0))
  rw [hlog 0 h0] at hd'
  convert hd' using 1
  ring

/-- A fixed Schottky constant suffices when the centre value has norm at most one. -/
noncomputable def cuspConstant : ℝ :=
  max 1 (1 + Real.log (FunctionTheory.schottkyZeroOneMajorant 1 (1 / 2)))

theorem cuspConstant_pos : 0 < cuspConstant := lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- The zero-and-one omission estimate has the correct logarithmic order at a cusp. -/
theorem norm_deriv_le_cusp_bound {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hzero : ∀ z ∈ ball 0 1, f z ≠ 0) (hone : ∀ z ∈ ball 0 1, f z ≠ 1)
    (hbase : ‖f 0‖ ≤ 1) :
    ‖deriv f 0‖ ≤ 8 * ‖f 0‖ * (cuspConstant - Real.log ‖f 0‖) := by
  have hsub : ball (0 : ℂ) (1 / 2) ⊆ ball 0 1 := ball_subset_ball (by norm_num)
  have hb : ∀ z ∈ ball (0 : ℂ) (1 / 2),
      ‖f z‖ ≤ FunctionTheory.schottkyZeroOneMajorant 1 (1 / 2) := by
    intro z hz
    exact FunctionTheory.norm_le_schottkyZeroOneMajorant (by norm_num) (by norm_num)
      (hf.analyticOnNhd isOpen_ball) hzero hone hbase (mem_ball_zero_iff.mp hz).le
  have hd := norm_deriv_le_of_zero_free_bounded (by norm_num : (0 : ℝ) < 1 / 2)
    (hf.mono hsub) (fun z hz => hzero z (hsub hz)) hb
  have hc : 1 + Real.log (FunctionTheory.schottkyZeroOneMajorant 1 (1 / 2)) ≤
      cuspConstant := le_max_right _ _
  calc
    ‖deriv f 0‖ ≤ 8 * ‖f 0‖ *
        (1 + Real.log (FunctionTheory.schottkyZeroOneMajorant 1 (1 / 2)) - Real.log ‖f 0‖) := by
      convert hd using 1
      ring
    _ ≤ 8 * ‖f 0‖ * (cuspConstant - Real.log ‖f 0‖) := by gcongr

/-- A universal lower cusp bound for every disc-covered plane domain omitting 0 and 1. -/
theorem IsHolomorphicDiscCovering.density_lower_cusp {p : ℂ → ℂ} {S : Set ℂ}
    (hp : IsHolomorphicDiscCovering p S) (hzero : (0 : ℂ) ∉ S) (hone : (1 : ℂ) ∉ S)
    {z : ℂ} (hz : z ∈ S) (hzn : ‖z‖ ≤ 1) :
    1 / (4 * ‖z‖ * (cuspConstant - Real.log ‖z‖)) ≤ coveringDensity p z := by
  obtain ⟨g, hg, hgm, hg0, he⟩ := hp.density_extremal hz
  have hd := norm_deriv_le_cusp_bound hg
    (fun w hw hh => hzero (hh ▸ hgm hw)) (fun w hw hh => hone (hh ▸ hgm hw))
    (by simpa [hg0] using hzn)
  rw [hg0] at hd
  have hzp : 0 < ‖z‖ := norm_pos_iff.mpr (ne_of_mem_of_not_mem hz hzero)
  have hlog : Real.log ‖z‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) hzn
  have hden : 0 < 4 * ‖z‖ * (cuspConstant - Real.log ‖z‖) := by
    have : 0 < cuspConstant - Real.log ‖z‖ := by linarith [cuspConstant_pos]
    positivity
  apply (div_le_iff₀ hden).mpr
  have hm := mul_le_mul_of_nonneg_left hd (hp.density_pos hz).le
  rw [he] at hm
  nlinarith

/-- A simple exponential test disc gives the upper bound needed at an isolated puncture.
The constant 2 is not sharp and is sufficient for the logarithmic asymptotics. -/
theorem IsHolomorphicDiscCovering.density_upper_cusp {p : ℂ → ℂ} {S : Set ℂ}
    (hp : IsHolomorphicDiscCovering p S) {a z : ℂ} {R : ℝ}
    (hball : ball a R \ {a} ⊆ S) (hz : z ≠ a) (hzR : ‖z - a‖ < R) :
    coveringDensity p z ≤ 2 / (‖z - a‖ * Real.log (R / ‖z - a‖)) := by
  have hr : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hR : 0 < R := hr.trans hzR
  let L : ℝ := Real.log (R / ‖z - a‖)
  have hL : 0 < L := Real.log_pos ((one_lt_div hr).mpr hzR)
  let g : ℂ → ℂ := fun w => a + (z - a) * Complex.exp ((L : ℂ) * w)
  have hg : Differentiable ℂ g := by dsimp [g]; fun_prop
  have hg0 : g 0 = z := by simp [g]
  have hgm : MapsTo g (ball 0 1) S := by
    intro w hw
    apply hball
    have he : g w - a = (z - a) * Complex.exp ((L : ℂ) * w) := by dsimp [g]; ring
    have hn : ‖g w - a‖ = ‖z - a‖ * Real.exp (L * w.re) := by
      rw [he, norm_mul, Complex.norm_exp]
      congr 2
      simp
    have hwre : w.re < 1 := (Complex.re_le_norm w).trans_lt (mem_ball_zero_iff.mp hw)
    have hnorm : ‖g w - a‖ < R := by
      rw [hn]
      calc
        ‖z - a‖ * Real.exp (L * w.re) < ‖z - a‖ * Real.exp L := by gcongr; nlinarith
        _ = R := by dsimp [L]; rw [Real.exp_log (div_pos hR hr)]; field_simp
    refine ⟨?_, ?_⟩
    · simpa only [mem_ball, dist_eq_norm] using hnorm
    · simp only [mem_singleton_iff]
      intro h
      have hnz : g w - a ≠ 0 := by rw [he]; exact mul_ne_zero (sub_ne_zero.mpr hz) (Complex.exp_ne_zero _)
      exact hnz (sub_eq_zero.mpr h)
  have hd : deriv g 0 = (z - a) * (L : ℂ) := by
    have h := ((hasDerivAt_id (0 : ℂ)).const_mul (L : ℂ)).cexp.const_mul (z - a)
    have h' := h.const_add a
    simpa [g] using h'.deriv
  have hs := hp.density_schwarz hg.differentiableOn hgm
  rw [hg0, hd, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL] at hs
  exact (le_div_iff₀ (mul_pos hr hL)).mpr hs

end AreaDeficit
