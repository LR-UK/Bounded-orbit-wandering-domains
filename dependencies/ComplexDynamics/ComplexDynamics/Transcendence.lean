import ComplexDynamics.Basic
import Mathlib.Topology.Algebra.Polynomial

/-! # A criterion for transcendence using escaping and bounded values -/

open Set Function Filter Polynomial
open scoped Topology

namespace ComplexDynamics

/-- An entire function with an escaping orbit and bounded values along a
sequence tending to infinity is transcendental. This criterion is useful for
approximation constructions with distant regions mapped into a fixed disk. -/
theorem isTranscendentalEntire_of_escape_and_bounded_values {f : ℂ → ℂ}
    (hf : IsEntire f) {z : ℂ} (hz : z ∈ escapingSet f)
    (u : ℕ → ℂ) (hu : Tendsto (fun n => ‖u n‖) atTop atTop)
    (C : ℝ) (hbound : ∀ n, ‖f (u n)‖ ≤ C) : IsTranscendentalEntire f := by
  refine ⟨hf, ?_⟩
  rintro ⟨p, hp⟩
  have hdeg : p.degree ≤ 0 := by
    apply le_of_not_gt
    intro hd
    have H := (p.tendsto_norm_atTop hd hu).eventually (eventually_ge_atTop (C + 1))
    obtain ⟨n, hn⟩ := H.exists
    rw [← hp] at hn
    have Hb := hbound n
    linarith
  have hconstant (w : ℂ) : f w = p.coeff 0 := by
    rw [hp, eq_C_of_degree_le_zero hdeg, eval_C, coeff_C_zero]
  have H : ∀ᶠ n : ℕ in atTop, ‖p.coeff 0‖ + 1 ≤ ‖(f^[n]) z‖ :=
    hz.eventually (eventually_ge_atTop (‖p.coeff 0‖ + 1))
  obtain ⟨n, hn, hlarge⟩ := ((eventually_ge_atTop 1).and H).exists
  cases n with
  | zero => omega
  | succ n =>
    rw [iterate_succ_apply', hconstant] at hlarge
    linarith

end ComplexDynamics
