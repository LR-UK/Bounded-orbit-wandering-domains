import EremenkosConjecture.DiscGeometry
import Mathlib.Topology.Algebra.Polynomial

/-!
# Transcendence from the disk itinerary and trapping

Along the prescribed orbit, the displacement `f(z)-z` stays bounded while
`z` tends to infinity. If `f` were a polynomial, `f-X` would therefore be
constant. A translation cannot send a closed disk into its own interior.
-/

open Set Metric Function Filter Polynomial
open scoped Topology

namespace EremenkosConjecture

theorem transcendental_of_targetDiscs_and_trapping (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (z : ℂ)
    (horbit : ∀ n, (f^[n]) z ∈ targetDisc n)
    (htrap : MapsTo f (controlDisc 0) trappingDisc) :
    ComplexDynamics.IsTranscendentalEntire f := by
  refine ⟨hf, ?_⟩
  rintro ⟨p, hp⟩
  let q : Polynomial ℂ := p - X
  have hescape : Tendsto (fun n => ‖(f^[n]) z‖) atTop atTop :=
    (escapesUniformlyOn_of_targetDiscs f {z}
      (fun n w hw => mem_singleton_iff.mp hw ▸ horbit n)).subset_escapingSet (mem_singleton z)
  have hbound (n : ℕ) : ‖q.eval ((f^[n]) z)‖ < 5 := by
    have h₁ : ‖(f^[n]) z - ((3 * n : ℝ) : ℂ)‖ < 1 := by
      simpa only [targetDisc, mem_ball, dist_eq_norm] using horbit n
    have h₂ : ‖(f^[n + 1]) z - ((3 * (n + 1 : ℕ) : ℝ) : ℂ)‖ < 1 := by
      simpa only [targetDisc, mem_ball, dist_eq_norm] using horbit (n + 1)
    have heq : q.eval ((f^[n]) z) =
        ((f^[n + 1]) z - ((3 * (n + 1 : ℕ) : ℝ) : ℂ)) -
          ((f^[n]) z - ((3 * n : ℝ) : ℂ)) + 3 := by
      simp only [q, eval_sub, eval_X, ← hp, iterate_succ_apply']
      push_cast
      ring
    rw [heq]
    have H := (norm_add_le
      (((f^[n + 1]) z - ((3 * (n + 1 : ℕ) : ℝ) : ℂ)) -
        ((f^[n]) z - ((3 * n : ℝ) : ℂ))) (3 : ℂ)).trans
      (add_le_add (norm_sub_le _ _) le_rfl)
    rw [show ‖(3 : ℂ)‖ = (3 : ℝ) by norm_num] at H
    linarith
  have hdeg : q.degree ≤ 0 := by
    by_contra h
    have hlim := q.tendsto_norm_atTop (lt_of_not_ge h) hescape
    obtain ⟨n, hn⟩ := (hlim.eventually (eventually_ge_atTop 5)).exists
    exact (not_lt_of_ge hn) (hbound n)
  have hq : q = C (q.coeff 0) := eq_C_of_degree_le_zero hdeg
  have htranslate (w : ℂ) : f w = w + q.coeff 0 := by
    have H := congrArg (fun a : Polynomial ℂ => a.eval w) hq
    simp only [q, eval_sub, eval_X, eval_C, ← hp] at H
    exact sub_eq_iff_eq_add.mp H |>.trans (add_comm _ _)
  have hright : (-2 : ℂ) ∈ controlDisc 0 := by
    norm_num [controlDisc, mem_closedBall, dist_eq_norm]
  have hleft : (-4 : ℂ) ∈ controlDisc 0 := by
    norm_num [controlDisc, mem_closedBall, dist_eq_norm]
  have h₁ := htrap hright
  have h₂ := htrap hleft
  simp only [trappingDisc, mem_ball, dist_eq_norm, htranslate] at h₁ h₂
  have H := norm_sub_le ((-2 : ℂ) + q.coeff 0 - (-3)) ((-4 : ℂ) + q.coeff 0 - (-3))
  have heq : ((-2 : ℂ) + q.coeff 0 - (-3)) - ((-4 : ℂ) + q.coeff 0 - (-3)) = 2 := by ring
  rw [heq] at H
  rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num] at H
  linarith

end EremenkosConjecture
