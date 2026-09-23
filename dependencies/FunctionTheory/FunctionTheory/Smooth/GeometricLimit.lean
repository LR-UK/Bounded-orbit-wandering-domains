import FunctionTheory.Smooth.ComplexSequenceLimit
import FunctionTheory.Smooth.FiniteSmoothNorm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Set Filter
open scoped Topology ContDiff

namespace FunctionTheory

set_option autoImplicit false

/-- A geometric bound on successive finite smooth norms gives a global
smooth complex-differentiable limit, with its uniform finite smooth norm
explicitly controlled. Holomorphy is only needed pointwise on the model set. -/
theorem exists_smooth_complex_limit_of_geometric_Cm_steps
    (F : ℕ → ℂ → ℂ) (hF : ∀ i, ContDiff ℝ ∞ (F i))
    (hF0 : ∀ z, F 0 z = z) (M : ℕ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hstep : ∀ i,
      finiteSmoothNormOn (max M (i + 1)) (fun z => F (i + 1) z - F i z) univ <
        ENNReal.ofReal (r / 2 / 2 ^ i))
    (K : Set ℂ) (hcomplex : ∀ i, ∀ a ∈ K, DifferentiableAt ℂ (F i) a) :
    ∃ e : ℂ ≃ₜ ℂ,
      ContDiff ℝ ∞ (e : ℂ → ℂ) ∧ ContDiff ℝ ∞ (e.symm : ℂ → ℂ) ∧
      TendstoUniformly F (e : ℂ → ℂ) atTop ∧
      finiteSmoothNormOn M (fun z => e z - z) univ ≤
        ENNReal.ofReal ((M + 1 : ℕ) * r) ∧
      (∀ A : Set ℂ, (∀ i, EqOn (F i) id A) → EqOn (e : ℂ → ℂ) id A) ∧
      ∀ a ∈ K, DifferentiableAt ℂ (e : ℂ → ℂ) a := by
  let q := max M 1
  let v : ℕ → ℝ := fun i => r / 2 / 2 ^ i
  have hv : Summable v := summable_geometric_two' r
  have Hsum : (∑' i, v i) = r := tsum_geometric_two' r
  have Hbound : ∀ j i, j ≤ max q (i + 1) → ∀ z,
      ‖iteratedFDeriv ℝ j (fun w => F (i + 1) w - F i w) z‖ ≤ v i := by
    intro j i hj z
    apply norm_iteratedFDeriv_le_of_finiteSmoothNormOn_le
      (show 0 ≤ r / 2 / 2 ^ i by positivity) (hstep i).le
    · dsimp [q] at hj
      omega
    · exact mem_univ z
  obtain ⟨e, he, hei, hconv, hnorm, hfix, hcomp⟩ :=
    exists_smooth_complex_diffeomorphism_limit_of_close_sequence
      F hF hF0 q (le_max_right M 1) v hv Hbound (by rw [Hsum]; exact hr1) K hcomplex
  refine ⟨e, he, hei, hconv, ?_, hfix, hcomp⟩
  apply finiteSmoothNormOn_le_of_uniform_bound hr.le
  intro j hj z _
  rw [← Hsum]
  exact hnorm j (hj.trans (le_max_left M 1)) z

end FunctionTheory
