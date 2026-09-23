import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic

open Set Metric Filter Function
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- Removing a countable set from a nonempty plane disc leaves it path
connected. Transfer Mathlib's plane theorem through its ball homeomorphism. -/
theorem isPathConnected_ball_sdiff_countable {S : Set ℂ} (hS : S.Countable)
    (c : ℂ) {r : ℝ} (hr : 0<r) : IsPathConnected (ball c r \ S) := by
  let e : OpenPartialHomeomorph ℂ ℂ := OpenPartialHomeomorph.univBall c r
  have hi : Injective e := by
    intro x y hxy
    exact e.injOn (by simp [e]) (by simp [e]) hxy
  have hc : IsPathConnected (e ⁻¹' S)ᶜ :=
    (hS.preimage hi).isPathConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num)
  have heq : e '' (e ⁻¹' S)ᶜ=ball c r \ S := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      refine ⟨?_,hw⟩
      have h := e.map_source (show w∈e.source by simp [e])
      simpa only [e,OpenPartialHomeomorph.univBall_target c hr] using h
    · rintro ⟨hz,hzS⟩
      have hzT : z∈e.target := by simpa only [e,OpenPartialHomeomorph.univBall_target c hr] using hz
      refine ⟨e.symm z,?_,e.right_inv hzT⟩
      simpa only [mem_compl_iff,mem_preimage,e.right_inv hzT] using hzS
  rw [← heq]
  exact hc.image (OpenPartialHomeomorph.continuous_univBall c r)

end FunctionTheory
