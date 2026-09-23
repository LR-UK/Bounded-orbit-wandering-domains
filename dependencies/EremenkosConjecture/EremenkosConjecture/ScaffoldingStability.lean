import EremenkosConjecture.ScaffoldingApproximation
import EremenkosConjecture.UniformUnivalence

/-! # Uniform injectivity, coverage, and derivative bounds on the strips -/

open Set Metric Function Complex

namespace EremenkosConjecture.Scaffolding

def openInsetSourceStrip (j : ℕ) : Set ℂ :=
  {z | height j - 3 / 5 < 4 * z.im ∧ 4 * z.im < height j + 13 / 5}

theorem isOpen_openInsetSourceStrip (j : ℕ) : IsOpen (openInsetSourceStrip j) :=
  (isOpen_lt continuous_const (continuous_const.mul Complex.continuous_im)).inter
    (isOpen_lt (continuous_const.mul Complex.continuous_im) continuous_const)

theorem openInsetSourceStrip_subset (j : ℕ) : openInsetSourceStrip j ⊆ insetSourceStrip j :=
  fun _ h => ⟨h.1.le, h.2.le⟩

theorem ball_inset_subset_source {j : ℕ} {z : ℂ} (hz : z ∈ insetSourceStrip j) :
    ball z (1 / 10) ⊆ sourceStrip j := by
  intro w hw
  have him : |w.im - z.im| < (1 / 10 : ℝ) := by
    simpa only [sub_im] using
      (abs_im_le_norm (w - z)).trans_lt (mem_ball_iff_norm.mp hw)
  obtain ⟨hlo, hhi⟩ := abs_lt.mp him
  constructor <;> linarith [hz.1, hz.2]

theorem closedBall_preimage_subset_openInset {j : ℕ} {y : ℂ}
    (hy : y ∈ sourceStrip (j + 1) ∪ targetStrip (j + 1)) :
    closedBall (y / 5) (1 / 20) ⊆ openInsetSourceStrip j := by
  intro z hz
  have him : |z.im - y.im / 5| ≤ (1 / 20 : ℝ) := by
    have H := (abs_im_le_norm (z - y / 5)).trans (mem_closedBall_iff_norm.mp hz)
    simpa using H
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  rcases hy with hy | hy
  · have hylo := hy.1
    have hyhi := hy.2
    rw [height_succ] at hylo hyhi
    constructor <;> linarith
  · have hylo := hy.1
    have hyhi := hy.2
    rw [height_succ] at hylo hyhi
    constructor <;> linarith

theorem normalized_close {f : ℂ → ℂ}
    (hclose : ∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100) :
    ∀ z ∈ sourceStrips, ‖f z / 5 - z‖ ≤ (1 / 500 : ℝ) := by
  intro z hz
  have heq : f z / 5 - z = (f z - 5 * z) / 5 := by ring
  rw [heq, norm_div]
  norm_num
  have H := hclose z hz
  linarith

theorem injective_on_inset_sourceStrip {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f sourceStrips)
    (hclose : ∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100) (j : ℕ) :
    InjOn f (insetSourceStrip j) := by
  have hg : DifferentiableOn ℂ (fun z => f z / 5) sourceStrips := hf.div_const 5
  have htube : ∀ z ∈ insetSourceStrip j, ball z (1 / 10) ⊆ sourceStrips :=
    fun z hz => (ball_inset_subset_source hz).trans (subset_iUnion _ j)
  have hinj := injOn_of_close_to_id (by norm_num : 0 < (1 / 10 : ℝ))
    (by norm_num : 2 * (1 / 500 : ℝ) < 1 / 10) htube hg
    (fun z hz => by simpa only [dist_eq_norm] using normalized_close hclose z hz)
  intro z hz w hw heq
  apply hinj hz hw
  exact congrArg (fun v : ℂ => v / 5) heq

theorem next_strips_subset_image {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f sourceStrips)
    (hclose : ∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100) (j : ℕ) :
    sourceStrip (j + 1) ∪ targetStrip (j + 1) ⊆ f '' openInsetSourceStrip j := by
  intro y hy
  have hb := closedBall_preimage_subset_openInset hy
  have hU : closedBall (y / 5) (1 / 20) ⊆ sourceStrips :=
    hb.trans ((openInsetSourceStrip_subset j).trans
      ((insetSourceStrip_subset j).trans (subset_iUnion _ j)))
  obtain ⟨w, hw, heq⟩ := exists_preimage_of_close_to_id_on_closedBall
    (hf.div_const 5) (by norm_num : 0 < (1 / 20 : ℝ))
    (by norm_num : (1 / 500 : ℝ) < (1 / 20) / 4) hU (normalized_close hclose)
  refine ⟨w, hb hw, ?_⟩
  have H := congrArg (fun v : ℂ => v * 5) heq
  simpa only [div_mul_cancel₀ _ (by norm_num : (5 : ℂ) ≠ 0)] using H

theorem derivative_bounds_on_inset {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f sourceStrips)
    (hclose : ∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100)
    {j : ℕ} {z : ℂ} (hz : z ∈ insetSourceStrip j) :
    2 ≤ ‖deriv f z‖ ∧ ‖deriv f z‖ ≤ 8 := by
  have hb : ball z (1 / 10) ⊆ sourceStrips :=
    (ball_inset_subset_source hz).trans (subset_iUnion _ j)
  have ha : DifferentiableOn ℂ (fun w : ℂ => 5 * w) (ball z (1 / 10)) :=
    ((differentiable_const (5 : ℂ)).mul differentiable_id).differentiableOn
  have H := norm_deriv_sub_le_of_close_on_ball (by norm_num : 0 < (1 / 10 : ℝ))
    (hf.mono hb) ha (fun w hw => hclose w (hb hw))
  have hd : deriv (fun w : ℂ => 5 * w) z = 5 := by
    simpa using ((hasDerivAt_id z).const_mul (5 : ℂ)).deriv
  rw [hd] at H
  have hlow := norm_sub_norm_le (5 : ℂ) (deriv f z)
  have hhigh := norm_sub_norm_le (deriv f z) (5 : ℂ)
  rw [norm_sub_rev] at hlow
  norm_num at H hlow hhigh
  constructor <;> linarith

end EremenkosConjecture.Scaffolding
