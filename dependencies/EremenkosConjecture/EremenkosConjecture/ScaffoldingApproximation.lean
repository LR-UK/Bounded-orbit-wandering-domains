import EremenkosConjecture.ScaffoldingGeometry
import ComplexApproximation.Arakelian

/-!
# The initial entire approximation in Section 4

The target equals `5z` on the closed source strips and zero on the trapping
disk. It is holomorphic on a neighbourhood of their union. The exact
Arakelian hypotheses are supplied by `ScaffoldingGeometry`.
-/

open Set Metric Complex ComplexApproximation
open scoped Topology

namespace EremenkosConjecture.Scaffolding

noncomputable def initialTarget (z : ℂ) : ℂ :=
  if z.im < (3 / 4 : ℝ) then 0 else 5 * z

def initialDomain : Set ℂ := {z | z.im < (3 / 4 : ℝ)} ∪ {z | (3 / 4 : ℝ) < z.im}

theorem isOpen_initialDomain : IsOpen initialDomain :=
  (isOpen_lt Complex.continuous_im continuous_const).union
    (isOpen_lt continuous_const Complex.continuous_im)

theorem im_lt_three_quarters_of_mem_trappingDisk {z : ℂ} (hz : z ∈ trappingDisk) :
    z.im < (3 / 4 : ℝ) := by
  have hn : ‖z‖ ≤ 1 / 2 := mem_closedBall_zero_iff.mp hz
  have hi := (le_abs_self z.im).trans (abs_im_le_norm z)
  linarith

theorem initialApproximationSet_subset_initialDomain : initialApproximationSet ⊆ initialDomain := by
  rintro z (hz | hz)
  · right
    have h := one_le_im_of_mem_closedSourceStrips hz
    change (3 / 4 : ℝ) < z.im
    linarith
  · exact Or.inl (im_lt_three_quarters_of_mem_trappingDisk hz)

theorem differentiableOn_initialTarget : DifferentiableOn ℂ initialTarget initialDomain := by
  intro z hz
  rcases hz with hz | hz
  · apply ((differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [Complex.continuous_im.continuousAt.eventually_lt_const hz] with w hw
    simp [initialTarget, hw]
  · have ha : DifferentiableAt ℂ (fun w : ℂ => 5 * w) z :=
      (differentiableAt_const _).mul differentiableAt_id
    apply (ha.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [Complex.continuous_im.continuousAt.eventually_const_lt hz] with w hw
    simp [initialTarget, not_lt_of_ge hw.le]

theorem initialTarget_eq_affine {z : ℂ} (hz : z ∈ closedSourceStrips) :
    initialTarget z = 5 * z := by
  have h := one_le_im_of_mem_closedSourceStrips hz
  simp [initialTarget, show ¬z.im < (3 / 4 : ℝ) by linarith]

theorem initialTarget_eq_zero {z : ℂ} (hz : z ∈ trappingDisk) : initialTarget z = 0 := by
  simp [initialTarget, im_lt_three_quarters_of_mem_trappingDisk hz]

/-- Equation (4.3), with an arbitrary positive tolerance. -/
theorem exists_initial_entire (ε : ℝ) (hε : 0 < ε) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      (∀ z ∈ closedSourceStrips, ‖f z - 5 * z‖ < ε) ∧
      (∀ z ∈ trappingDisk, ‖f z‖ < ε) := by
  obtain ⟨f, hf, herr⟩ := arakelian_approximation_of_holomorphic
    initialApproximationSet isArakelian_initialApproximationSet
    initialDomain isOpen_initialDomain initialApproximationSet_subset_initialDomain
    initialTarget differentiableOn_initialTarget ε hε
  refine ⟨f, hf, ?_, ?_⟩
  · intro z hz
    simpa only [initialTarget_eq_affine hz] using herr z (Or.inl hz)
  · intro z hz
    simpa only [initialTarget_eq_zero hz, sub_zero] using herr z (Or.inr hz)

/-- The bounded trapping property (4.4) persists under the next approximation. -/
theorem mapsTo_trappingDisk_of_close {f g : ℂ → ℂ} {ε : ℝ} (hε : ε ≤ 1 / 5)
    (hf : ∀ z ∈ trappingDisk, ‖f z‖ < ε)
    (hgf : ∀ z ∈ trappingDisk, ‖g z - f z‖ ≤ ε) :
    MapsTo g trappingDisk (ball 0 (1 / 2)) := by
  intro z hz
  rw [mem_ball_zero_iff]
  have hnorm : ‖g z‖ ≤ ‖g z - f z‖ + ‖f z‖ := by
    simpa only [norm_sub_rev, add_comm] using norm_le_insert (f z) (g z)
  have h1 := hf z hz
  have h2 := hgf z hz
  linarith

/-- The real-part expansion conclusion of Lemma 4.1. -/
theorem real_part_expansion {f : ℂ → ℂ} {z : ℂ} {ε : ℝ}
    (hε : ε < 1) (hclose : ‖f z - 5 * z‖ ≤ ε) (hz : 1 ≤ |z.re|) :
    4 * |z.re| < |(f z).re| := by
  have hre : |(f z).re - 5 * z.re| ≤ ε := by
    simpa using (abs_re_le_norm (f z - 5 * z)).trans hclose
  have hnorm := abs_sub_abs_le_abs_sub (5 * z.re) (f z).re
  rw [abs_sub_comm, abs_mul] at hnorm
  norm_num at hnorm
  linarith

end EremenkosConjecture.Scaffolding
