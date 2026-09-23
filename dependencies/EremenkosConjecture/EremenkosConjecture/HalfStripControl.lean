import ComplexApproximation.HalfStripBounds
import EremenkosConjecture.ConformalEmbedding
import EremenkosConjecture.IterateApproximation

/-! # Neighbourhood control of the half-strip map -/

open Set Metric Complex
open scoped Real Topology NNReal

namespace EremenkosConjecture

namespace HalfStrip

open ComplexApproximation.HalfStrip

def closedInset (η b : ℝ) : Set ℂ := {z | η ≤ z.re ∧ |z.im| ≤ b}

theorem isClosed_closedInset (η b : ℝ) : IsClosed (closedInset η b) :=
  (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_le Complex.continuous_im.abs continuous_const)

theorem closedInset_subset_domain {η b : ℝ} (hη : 0 < η) (hb : b < Real.pi / 2) :
    closedInset η b ⊆ domain := fun _ hz => ⟨hη.trans_le hz.1, hz.2.trans_lt hb⟩

theorem exists_uniform_tube {η b : ℝ} (hη : 0 < η) (hb : b < Real.pi / 2) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ closedInset η b, ball z r ⊆ truncated (η / 2) := by
  refine ⟨min (η / 2) ((Real.pi / 2 - b) / 2),
    lt_min (half_pos hη) (half_pos (sub_pos.mpr hb)), ?_⟩
  intro z hz w hw
  have hd : ‖w - z‖ < min (η / 2) ((Real.pi / 2 - b) / 2) := by
    simpa only [mem_ball, dist_eq_norm] using hw
  have hr := (Complex.abs_re_le_norm (w - z)).trans_lt hd
  have hi := (Complex.abs_im_le_norm (w - z)).trans_lt hd
  simp only [Complex.sub_re, Complex.sub_im] at hr hi
  have hwr : η / 2 ≤ w.re := by
    have := (abs_lt.mp (hr.trans_le (min_le_left _ _))).1
    linarith [hz.1]
  have hwi : |w.im| < Real.pi / 2 := by
    have ht := abs_add_le (w.im - z.im) z.im
    rw [sub_add_cancel] at ht
    have hi' := hi.trans_le (min_le_right _ _)
    linarith [hz.2]
  exact ⟨⟨(half_pos hη).trans_le hwr, hwi⟩, hwr⟩

/-- The map is controlled on a whole uniform neighbourhood of the closed
half-strip, which is the hypothesis needed for unbounded iterate stability. -/
theorem uniformControlOn_closedInset {η b : ℝ} (hη : 0 < η) (hb : b < Real.pi / 2) :
    UniformControlOn ComplexApproximation.HalfStrip.map domain (closedInset η b) := by
  obtain ⟨r, hr, htube⟩ := exists_uniform_tube hη hb
  obtain ⟨C, hC, hLip⟩ := exists_lipschitzOn_truncated (half_pos hη)
  intro ε hε
  refine ⟨min r (ε / ((C : ℝ) + 1)),
    lt_min hr (div_pos hε (by positivity)), ?_⟩
  intro x hx y hy
  have hyT := htube x hx (hy.trans_le (min_le_left _ _))
  have hxT := htube x hx (mem_ball_self hr)
  refine ⟨hyT.1, ?_⟩
  have hle := hLip.dist_le_mul y hyT x hxT
  have hsmall := (lt_div_iff₀ (by positivity : 0 < (C : ℝ) + 1)).mp
    (hy.trans_le (min_le_right _ _))
  exact hle.trans_lt (by nlinarith [dist_nonneg (x := y) (y := x)])

theorem exists_conformal_chart : ∃ e : OpenPartialHomeomorph ℂ ℂ,
    e.source = domain ∧ e.target = ComplexApproximation.HalfStrip.map '' domain ∧
    (∀ z, e z = ComplexApproximation.HalfStrip.map z) ∧
    DifferentiableOn ℂ e.symm e.target :=
  exists_conformal_chart_of_injOn isOpen_domain differentiableOn_map injOn_map
    (fun _ hz => deriv_map_ne_zero hz)

end HalfStrip

end EremenkosConjecture
