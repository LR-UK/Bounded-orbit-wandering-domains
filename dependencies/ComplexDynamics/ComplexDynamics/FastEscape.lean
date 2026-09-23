import ComplexDynamics.Basic
import Mathlib.Analysis.Complex.AbsMax

/-!
# Maximum modulus and fast escape

The maximum modulus is initially defined on the closed disk. For entire
functions this equals the supremum on the boundary circle, as proved below.
Fast escape at a specified radius retains that radius explicitly. The
radius-free set quantifies over the radii permitted in the paper: positive
radii whose open disk meets the Julia set.
-/

open Set Metric Function

namespace ComplexDynamics

noncomputable def maximumModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' closedBall 0 r)

theorem norm_le_maximumModulus {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ} {z : ℂ}
    (hz : z ∈ closedBall 0 r) : ‖f z‖ ≤ maximumModulus f r :=
  le_csSup ((isCompact_closedBall 0 r).image hf.norm).bddAbove (mem_image_of_mem _ hz)

theorem maximumModulus_le {f : ℂ → ℂ} {r C : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ z ∈ closedBall 0 r, ‖f z‖ ≤ C) : maximumModulus f r ≤ C := by
  apply csSup_le ((nonempty_closedBall.mpr hr).image _)
  rintro a ⟨z, hz, rfl⟩
  exact hbound z hz

theorem maximumModulus_nonneg {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ maximumModulus f r :=
  (norm_nonneg (f 0)).trans (norm_le_maximumModulus hf (mem_closedBall_self hr))

theorem maximumModulus_mono {f : ℂ → ℂ} (hf : Continuous f) {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) : maximumModulus f r ≤ maximumModulus f s :=
  maximumModulus_le hr (fun _ hz => norm_le_maximumModulus hf (closedBall_subset_closedBall hrs hz))

theorem maximumModulus_eq_sphere {f : ℂ → ℂ} (hf : IsEntire f) {r : ℝ} (hr : 0 ≤ r) :
    maximumModulus f r = sSup ((fun z => ‖f z‖) '' sphere 0 r) := by
  have hcircle : (sphere (0 : ℂ) r).Nonempty := by
    refine ⟨(r : ℂ), ?_⟩
    simp only [mem_sphere, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have hb : BddAbove ((fun z => ‖f z‖) '' sphere 0 r) :=
    ((isCompact_sphere 0 r).image hf.continuous.norm).bddAbove
  apply le_antisymm
  · apply maximumModulus_le hr
    intro z hz
    exact Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_closedBall
      hf.differentiableOn.diffContOnCl
      (fun w hw => le_csSup hb (mem_image_of_mem _ (frontier_closedBall_subset_sphere hw)))
      (subset_closure hz)
  · apply csSup_le (hcircle.image _)
    rintro a ⟨z, hz, rfl⟩
    exact norm_le_maximumModulus hf.continuous (sphere_subset_closedBall hz)

theorem maximumModulus_le_of_uniform_error {f g : ℂ → ℂ} (hg : Continuous g)
    {r δ : ℝ} (hr : 0 ≤ r) (hclose : ∀ z ∈ closedBall 0 r, ‖f z - g z‖ ≤ δ) :
    maximumModulus f r ≤ maximumModulus g r + δ := by
  apply maximumModulus_le hr
  intro z hz
  have H := norm_le_norm_add_norm_sub (g z) (f z)
  rw [norm_sub_rev] at H
  have Hb := norm_le_maximumModulus hg hz
  have He := hclose z hz
  linarith

def fastEscapingSetAtRadius (f : ℂ → ℂ) (r : ℝ) : Set ℂ :=
  {z | z ∈ escapingSet f ∧ ∃ l : ℕ, ∀ n : ℕ,
    ((maximumModulus f)^[n]) r ≤ ‖(f^[n + l]) z‖}

def fastEscapingSet (f : ℂ → ℂ) : Set ℂ :=
  {z | ∃ r : ℝ, 0 < r ∧ (ball 0 r ∩ juliaSet f).Nonempty ∧ z ∈ fastEscapingSetAtRadius f r}

theorem maximumModulus_iterate_le {f : ℂ → ℂ} (hf : Continuous f)
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n) (hstep : ∀ n, maximumModulus f (r n) ≤ r (n + 1))
    (n : ℕ) : 0 ≤ ((maximumModulus f)^[n]) (r 0) ∧
      ((maximumModulus f)^[n]) (r 0) ≤ r n := by
  induction n with
  | zero => exact ⟨hr 0, le_rfl⟩
  | succ n ih =>
    rw [iterate_succ_apply']
    exact ⟨maximumModulus_nonneg hf ih.1,
      (maximumModulus_mono hf ih.1 ih.2).trans (hstep n)⟩

theorem mem_fastEscapingSetAtRadius_of_radius_sequence {f : ℂ → ℂ} (hf : Continuous f)
    {z : ℂ} (hz : z ∈ escapingSet f) (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n)
    (hstep : ∀ n, maximumModulus f (r n) ≤ r (n + 1)) (l : ℕ)
    (horbit : ∀ n, r n ≤ ‖(f^[n + l]) z‖) : z ∈ fastEscapingSetAtRadius f (r 0) :=
  ⟨hz, l, fun n => (maximumModulus_iterate_le hf r hr hstep n).2.trans (horbit n)⟩

end ComplexDynamics
