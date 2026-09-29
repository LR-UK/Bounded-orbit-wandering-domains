module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

public import EremenkoLyubichConstant.Koebe

@[expose] public section

/-!
# Expansion in logarithmic coordinates

This module isolates the exact quantitative step in Lemma 2.1 of Rempe,
*The Eremenko--Lyubich constant*.  The auxiliary map `g` is the exponential lift
constructed in the paper from a tract equivalence and the disc--half-plane Möbius map.
-/

open Set Metric Filter

namespace EremenkoLyubichConstant

noncomputable section

/-- The right half-plane with boundary real part `ρ`. -/
def rightHalfPlane (ρ : ℝ) : Set ℂ := {z | ρ < z.re}

/-- The logarithmic derivative identity obtained by differentiating
`exp ∘ F = f ∘ exp`, written as a norm identity. -/
theorem logarithmic_derivative_norm_identity_of_eventuallyEq
    {f F : ℂ → ℂ} {ζ : ℂ}
    (hfun : ∀ᶠ z in nhds ζ, Complex.exp (F z) = f (Complex.exp z))
    (hF : DifferentiableAt ℂ F ζ)
    (hf : DifferentiableAt ℂ f (Complex.exp ζ)) :
    ‖deriv F ζ‖ * ‖Complex.exp (F ζ)‖ =
      ‖deriv f (Complex.exp ζ)‖ * ‖Complex.exp ζ‖ := by
  have hleft : HasDerivAt (Complex.exp ∘ F)
      (Complex.exp (F ζ) * deriv F ζ) ζ :=
    (Complex.hasDerivAt_exp (F ζ)).comp ζ hF.hasDerivAt
  have hright : HasDerivAt (f ∘ Complex.exp)
      (deriv f (Complex.exp ζ) * Complex.exp ζ) ζ :=
    hf.hasDerivAt.comp ζ (Complex.hasDerivAt_exp ζ)
  have hevent : (Complex.exp ∘ F) =ᶠ[nhds ζ] (f ∘ Complex.exp) :=
    hfun
  have hder := hleft.unique (hright.congr_of_eventuallyEq hevent)
  have hn := congrArg norm hder
  simpa [norm_mul, mul_comm, mul_left_comm, mul_assoc] using hn

/-- The derivative norm identity for a globally stated logarithmic-transform identity. -/
theorem logarithmic_derivative_norm_identity
    {f F : ℂ → ℂ} {ζ : ℂ}
    (hfun : ∀ z, Complex.exp (F z) = f (Complex.exp z))
    (hF : DifferentiableAt ℂ F ζ)
    (hf : DifferentiableAt ℂ f (Complex.exp ζ)) :
    ‖deriv F ζ‖ * ‖Complex.exp (F ζ)‖ =
      ‖deriv f (Complex.exp ζ)‖ * ‖Complex.exp ζ‖ :=
  logarithmic_derivative_norm_identity_of_eventuallyEq (.of_forall hfun) hF hf

/-- Theorem 1.1, inequality (1.4), as the algebraic consequence of (1.3) and the
logarithmic derivative identity. -/
theorem expansion_in_original_coordinates
    {f F : ℂ → ℂ} {ρ : ℝ} {ζ : ℂ}
    (hlog : ((F ζ).re - ρ) / 2 ≤ ‖deriv F ζ‖)
    (hid : ‖deriv F ζ‖ * ‖Complex.exp (F ζ)‖ =
      ‖deriv f (Complex.exp ζ)‖ * ‖Complex.exp ζ‖) :
    (((F ζ).re - ρ) * ‖Complex.exp (F ζ)‖) / 2 ≤
      ‖deriv f (Complex.exp ζ)‖ * ‖Complex.exp ζ‖ := by
  rw [← hid]
  have hexp : 0 ≤ ‖Complex.exp (F ζ)‖ := norm_nonneg _
  nlinarith

end

end EremenkoLyubichConstant
