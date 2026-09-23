import FunctionTheory.Conformal.StableInverseBranch
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

open Set Metric Bornology

namespace FunctionTheory

set_option autoImplicit false

/-- An arbitrarily small source disc can be expanded affinely to cover any
bounded plane set, with derivative norm at least two. -/
theorem exists_expanding_affine_ball_cover {K : Set ℂ} (hK : IsBounded K)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ a : ℂ, 2 ≤ ‖a‖ ∧
      K ⊆ (fun z => a * (z-c)) '' ball c r := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hK
  let M : ℝ := max R 0 + 1
  have hM : 0 < M := by dsimp [M]; linarith [le_max_right R 0]
  let L : ℝ := 2 + M/r
  have hL : 2 < L := by dsimp [L]; linarith [div_pos hM hr]
  have hLp : 0 < L := by linarith
  have hLn : ‖(L : ℂ)‖ = L := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLp]
  refine ⟨(L : ℂ), by rw [hLn]; exact hL.le, ?_⟩
  intro w hw
  refine ⟨w/(L : ℂ)+c, ?_, ?_⟩
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_right, norm_div, hLn]
    apply (div_lt_iff₀ hLp).mpr
    have hLR : L*r = 2*r+M := by dsimp [L]; rw [add_mul, div_mul_cancel₀ M hr.ne']
    rw [mul_comm r L, hLR]
    have hwM : ‖w‖ < M := by
      dsimp [M]
      linarith [hR w hw, le_max_left R 0]
    linarith
  · have hne : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hLp.ne'
    dsimp
    rw [add_sub_cancel_right]
    field_simp

/-- Affine channels admit uniform approximation tolerances retaining
holomorphic inverse branches near the prescribed compact target. The forward
derivative is at least one on the image of each retained inverse branch. -/
theorem exists_stable_expanding_affine_channel {K : Set ℂ} (hK : IsCompact K)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ a : ℂ, 2 ≤ ‖a‖ ∧ ∃ δ > 0,
      ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f (ball c r) →
        (∀ z ∈ ball c r, dist (f z) (a*(z-c)) ≤ δ) →
        ∃ b : OpenPartialHomeomorph ℂ ℂ,
          K ⊆ b.source ∧ closure b.target ⊆ ball c r ∧ IsCompact (closure b.target) ∧
          AnalyticOnNhd ℂ b b.source ∧
          (∀ w ∈ b.source, f (b w) = w) ∧
          (∀ z ∈ b.target, b (f z) = z) ∧
          ∀ z ∈ b.target, 1 ≤ ‖deriv f z‖ := by
  obtain ⟨a, ha, hcover⟩ := exists_expanding_affine_ball_cover hK.isBounded c (half_pos hr)
  have ha0 : a ≠ 0 := by intro h; norm_num [h] at ha
  let φ : ℂ → ℂ := fun z => a*(z-c)
  have hφ : AnalyticOnNhd ℂ φ univ :=
    analyticOnNhd_const.mul (analyticOnNhd_id.sub analyticOnNhd_const)
  have hφi : Function.Injective φ := by
    intro z w h
    have H : z-c=w-c := mul_left_cancel₀ ha0 h
    exact sub_left_injective H
  have hφD : DifferentiableOn ℂ φ (ball c (r/2)) :=
    hφ.differentiableOn.mono (subset_univ _)
  let e := hφD.toOpenPartialHomeomorph isOpen_ball hφi.injOn
  have hei : DifferentiableOn ℂ e.symm e.target :=
    hφD.differentiableOn_toOpenPartialHomeomorph_symm isOpen_ball hφi.injOn
  obtain ⟨d₁, hd₁, Hbranch⟩ := exists_stable_inverse_branch_on_compact
    e hφD hei hK hcover
  obtain ⟨d₂, hd₂, Hderiv⟩ := exists_derivative_approximation_tolerance
    (ball c r) (closedBall c (r/2)) isOpen_ball (isCompact_closedBall _ _)
    (closedBall_subset_ball (half_lt_self hr)) 1 (by norm_num)
  have hsmall : ball c (r/2) ⊆ ball c r := ball_subset_ball (by linarith)
  refine ⟨a,ha,min d₁ d₂,lt_min hd₁ hd₂,?_⟩
  intro f hf hclose
  obtain ⟨b, hbK, hbS, hbC, hbA, hfb, hbf⟩ := Hbranch f (hf.mono hsmall)
    (fun z hz => (hclose z (hsmall hz)).trans (min_le_left _ _))
  refine ⟨b,hbK,hbS.trans hsmall,hbC,hbA,hfb,hbf,?_⟩
  intro z hz
  have hzsmall : z ∈ ball c (r/2) := hbS (subset_closure hz)
  have H := Hderiv f φ hf.differentiableOn (hφ.differentiableOn.mono (subset_univ _))
    (fun w hw => (hclose w hw).trans (min_le_right _ _)) z (ball_subset_closedBall hzsmall)
  have hdφ : deriv φ z = a := by
    have hd := ((hasDerivAt_id z).sub_const c).const_mul a
    simpa only [φ, id_eq, mul_one] using hd.deriv
  rw [hdφ] at H
  have Hnorm := norm_sub_norm_le a (deriv f z)
  rw [norm_sub_rev] at Hnorm
  linarith

end FunctionTheory
