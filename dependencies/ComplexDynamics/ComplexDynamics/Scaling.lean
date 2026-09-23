import ComplexDynamics.Wandering
import Mathlib.Topology.Algebra.GroupWithZero

/-! # Nonzero linear changes of coordinate -/

open Set Function Filter Polynomial
open scoped Topology

namespace ComplexDynamics

noncomputable def scaleConjugate (c : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ := c * f (c⁻¹ * z)

theorem iterate_scaleConjugate_mul (c : ℂ) (hc : c ≠ 0) (f : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    ((scaleConjugate c f)^[n]) (c * z) = c * (f^[n]) z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply']
    simp only [scaleConjugate, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem iterate_scaleConjugate (c : ℂ) (hc : c ≠ 0) (f : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    ((scaleConjugate c f)^[n]) z = c * (f^[n]) (c⁻¹ * z) := by
  simpa only [← mul_assoc, mul_inv_cancel₀ hc, one_mul] using
    iterate_scaleConjugate_mul c hc f n (c⁻¹ * z)

theorem IsEntire.scaleConjugate {f : ℂ → ℂ} (hf : IsEntire f) (c : ℂ) :
    IsEntire (scaleConjugate c f) :=
  (hf.comp (differentiable_id.const_mul c⁻¹)).const_mul c

theorem IsTranscendentalEntire.scaleConjugate {f : ℂ → ℂ} (hf : IsTranscendentalEntire f)
    (c : ℂ) (hc : c ≠ 0) : IsTranscendentalEntire (scaleConjugate c f) := by
  refine ⟨hf.1.scaleConjugate c, ?_⟩
  rintro ⟨p, hp⟩
  apply hf.2
  refine ⟨C c⁻¹ * p.comp (C c * X), fun z => ?_⟩
  have H := hp (c * z)
  change c * f (c⁻¹ * (c * z)) = p.eval (c * z) at H
  simp only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] at H
  simp only [eval_mul, eval_C, eval_comp, eval_X]
  rw [← H, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem EscapesUniformlyOn.scaleConjugate {f : ℂ → ℂ} {K : Set ℂ}
    (h : EscapesUniformlyOn f K) (c : ℂ) (hc : c ≠ 0) :
    EscapesUniformlyOn (scaleConjugate c f) ((fun z => c * z) '' K) := by
  intro R
  filter_upwards [h (R / ‖c‖)] with n hn w hw
  obtain ⟨z, hz, rfl⟩ := hw
  rw [iterate_scaleConjugate_mul c hc, norm_mul]
  have H := (div_lt_iff₀ (norm_pos_iff.mpr hc)).mp (hn z hz)
  simpa only [mul_comm] using H

theorem mapsTo_scale_trappedSet (f : ℂ → ℂ) (B : Set ℂ) (c : ℂ) (hc : c ≠ 0) :
    MapsTo (fun z => c * z) (trappedSet f B)
      (trappedSet (scaleConjugate c f) ((fun z => c * z) '' B)) := by
  intro z hz
  filter_upwards [hz] with n hn
  rw [iterate_scaleConjugate_mul c hc]
  exact mem_image_of_mem _ hn

end ComplexDynamics
