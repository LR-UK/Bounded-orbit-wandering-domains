import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

open Function

namespace FunctionTheory

set_option autoImplicit false

/-- A finite iterate has nonzero derivative if every step of its orbit
does. Only differentiability at the finitely many inputs is required. -/
theorem deriv_iterate_ne_zero_of_orbit {f : ℂ → ℂ} {z : ℂ} (n : ℕ)
    (ha : ∀ j<n, DifferentiableAt ℂ f ((f^[j]) z))
    (hd : ∀ j<n, deriv f ((f^[j]) z)≠0) :
    DifferentiableAt ℂ (f^[n]) z ∧ deriv (f^[n]) z≠0 := by
  induction n with
  | zero => simpa using And.intro (differentiableAt_id (𝕜 := ℂ) (x := z)) (one_ne_zero : (1 : ℂ)≠0)
  | succ n ih =>
    have H := ih (fun j hj => ha j (by omega)) (fun j hj => hd j (by omega))
    have hf := (ha n (by omega)).hasDerivAt.comp z H.1.hasDerivAt
    have hn : deriv f ((f^[n]) z) * deriv (f^[n]) z ≠0 := mul_ne_zero (hd n (by omega)) H.2
    rw [Function.iterate_succ']
    exact ⟨hf.differentiableAt,by rw [hf.deriv]; exact hn⟩

end FunctionTheory
