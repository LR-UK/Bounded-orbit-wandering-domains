import Runge.Holomorphic

/-!
# Polynomial separation of full compact sets

Runge approximation of the reciprocal kernel separates any point outside a
full compact set by a polynomial. This form is useful for constructing full
neighbourhoods by polynomial sublevel sets.
-/

open Set Polynomial

namespace Runge

theorem exists_polynomial_separator (K : Set ℂ) (hK : IsCompact K)
    (hfull : IsConnected Kᶜ) (a : ℂ) (ha : a ∉ K) :
    ∃ p : ℂ[X], p.eval a = 1 ∧ ∀ z ∈ K, ‖p.eval z‖ < 1 / 2 := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  let M : ℝ := R + ‖a‖
  have hM : 0 < M := add_pos_of_pos_of_nonneg hR (norm_nonneg a)
  have hKU : K ⊆ ({a} : Set ℂ)ᶜ := by
    intro z hz hza
    exact ha (Set.mem_singleton_iff.mp hza ▸ hz)
  have hg : DifferentiableOn ℂ (fun z : ℂ => (z - a)⁻¹) ({a}ᶜ) := by
    apply (differentiableOn_id.sub_const a).inv
    intro z hz
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, sub_ne_zero, id_eq] using hz
  obtain ⟨p, hp⟩ := polynomial_approximation_of_holomorphic K hK hfull {a}ᶜ
    isClosed_singleton.isOpen_compl hKU (fun z : ℂ => (z - a)⁻¹) hg
    (1 / (2 * M)) (by positivity)
  refine ⟨C 1 - (X - C a) * p, by simp, fun z hz => ?_⟩
  have hza : z - a ≠ 0 := sub_ne_zero.mpr (hKU hz)
  have hbound : ‖z - a‖ ≤ M := by
    have h₁ := norm_sub_le z a
    have h₂ := hKR z hz
    dsimp [M]
    linarith
  have hpoly : (C 1 - (X - C a) * p).eval z =
      (z - a) * ((z - a)⁻¹ - p.eval z) := by
    simp only [eval_sub, eval_C, eval_mul, eval_X]
    rw [mul_sub, mul_inv_cancel₀ hza]
  rw [hpoly, norm_mul]
  calc
    ‖z - a‖ * ‖(z - a)⁻¹ - p.eval z‖ ≤ M * ‖(z - a)⁻¹ - p.eval z‖ :=
      mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
    _ < M * (1 / (2 * M)) := mul_lt_mul_of_pos_left (hp z hz) hM
    _ = 1 / 2 := by field_simp

end Runge
