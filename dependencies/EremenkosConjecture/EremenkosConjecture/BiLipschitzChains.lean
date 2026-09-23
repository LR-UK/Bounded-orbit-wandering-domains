import EremenkosConjecture.UniformIterateControl

/-! # Composing quantitative ambient charts along an orbit -/

open Set Function
open scoped NNReal

namespace EremenkosConjecture

noncomputable def ambientChain (H : ℕ → ℂ ≃ₜ ℂ) : ℕ → ℂ ≃ₜ ℂ
  | 0 => Homeomorph.refl ℂ
  | n + 1 => (ambientChain H n).trans (H n)

theorem ambientChain_apply_succ (H : ℕ → ℂ ≃ₜ ℂ) (n : ℕ) (z : ℂ) :
    ambientChain H (n + 1) z = H n (ambientChain H n z) := rfl

theorem exists_lipschitz_ambientChain (H : ℕ → ℂ ≃ₜ ℂ)
    (hH : ∀ n, ∃ L L' : ℝ≥0, LipschitzWith L (H n) ∧ LipschitzWith L' (H n).symm)
    (n : ℕ) : ∃ L L' : ℝ≥0,
      LipschitzWith L (ambientChain H n) ∧ LipschitzWith L' (ambientChain H n).symm := by
  induction n with
  | zero => exact ⟨1, 1, LipschitzWith.id, LipschitzWith.id⟩
  | succ n ih =>
      obtain ⟨L, L', hL, hL'⟩ := ih
      obtain ⟨M, M', hM, hM'⟩ := hH n
      exact ⟨M * L, L' * M', hM.comp hL, hL'.comp hM'⟩

theorem ambientChain_eq_iterate {H : ℕ → ℂ ≃ₜ ℂ} {f : ℂ → ℂ} {U : ℕ → Set ℂ}
    (heq : ∀ k, EqOn f (H k) (U k)) {A : Set ℂ} {n : ℕ}
    (horbit : ∀ k < n, MapsTo (f^[k]) A (U k)) : EqOn (f^[n]) (ambientChain H n) A := by
  intro z hz
  have hpoint (k : ℕ) (hk : k ≤ n) : ambientChain H k z = (f^[k]) z := by
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [ambientChain_apply_succ, ih (by omega), ← heq k (horbit k (by omega) hz), iterate_succ_apply']
  exact (hpoint n le_rfl).symm

end EremenkosConjecture
