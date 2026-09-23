import ComplexDynamics.Transcendence
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Transcendental entire perturbations of polynomials -/

open Set Metric Polynomial

namespace ComplexDynamics

theorem isTranscendentalEntire_exp : IsTranscendentalEntire Complex.exp := by
  refine ⟨Complex.differentiable_exp, ?_⟩
  rintro ⟨p, hp⟩
  have hdeg : p.degree ≤ 0 := by
    apply le_of_not_gt
    intro hgt
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root p (ne_of_gt hgt)
    exact Complex.exp_ne_zero z ((hp z).trans hz)
  have hconst : Complex.exp = fun _ : ℂ => p.coeff 0 := by
    funext z
    rw [hp, eq_C_of_degree_le_zero hdeg, eval_C, coeff_C_zero]
  have H := congrArg (fun g : ℂ → ℂ => deriv g 0) hconst
  simpa using H

theorem isTranscendentalEntire_polynomial_add_exp (p : Polynomial ℂ) (a : ℂ) (ha : a ≠ 0) :
    IsTranscendentalEntire (fun z => p.eval z + a * Complex.exp z) := by
  refine ⟨p.differentiable.add (Complex.differentiable_exp.const_mul a), ?_⟩
  rintro ⟨q, hq⟩
  apply isTranscendentalEntire_exp.2
  refine ⟨C a⁻¹ * (q - p), fun z => ?_⟩
  simp only [eval_mul, eval_C, eval_sub]
  rw [← hq z, add_sub_cancel_left, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

/-- A polynomial can be approximated on a compact set by a transcendental
entire function, with an arbitrarily small positive uniform error. -/
theorem exists_transcendentalEntire_near_polynomial (p : Polynomial ℂ) (K : Set ℂ)
    (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧ ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  obtain ⟨R, hR, hbound⟩ := (hK.image Complex.continuous_exp).isBounded.exists_pos_norm_le
  let a : ℝ := ε / (2 * R)
  have ha : 0 < a := div_pos hε (by positivity)
  refine ⟨fun z => p.eval z + (a : ℂ) * Complex.exp z,
    isTranscendentalEntire_polynomial_add_exp p a (by exact_mod_cast (ne_of_gt ha)), ?_⟩
  intro z hz
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have H := mul_le_mul_of_nonneg_left (hbound _ (mem_image_of_mem _ hz)) ha.le
  have heq : a * R = ε / 2 := by dsimp [a]; field_simp
  rw [heq] at H
  linarith

end ComplexDynamics
