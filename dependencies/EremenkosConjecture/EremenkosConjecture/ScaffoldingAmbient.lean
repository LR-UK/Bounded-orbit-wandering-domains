import EremenkosConjecture.ScaffoldingBranches
import ComplexApproximation.HorizontalStripExtension

/-! # Quantitative ambient extensions of the Section 4 strip maps -/

open Set Metric Function ComplexApproximation
open scoped NNReal

namespace EremenkosConjecture.Scaffolding

theorem re_deriv_lower_bound_on_inset {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f sourceStrips)
    (hclose : ∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100)
    {j : ℕ} {z : ℂ} (hz : z ∈ insetSourceStrip j) : 2 ≤ (deriv f z).re := by
  have hb : ball z (1 / 10) ⊆ sourceStrips :=
    (ball_inset_subset_source hz).trans (subset_iUnion _ j)
  have ha : DifferentiableOn ℂ (fun w : ℂ => 5 * w) (ball z (1 / 10)) :=
    ((differentiable_const (5 : ℂ)).mul differentiable_id).differentiableOn
  have h := norm_deriv_sub_le_of_close_on_ball (by norm_num : 0 < (1 / 10 : ℝ))
    (hf.mono hb) ha (fun w hw => hclose w (hb hw))
  have hd : deriv (fun w : ℂ => 5 * w) z = 5 := by
    simpa using ((hasDerivAt_id z).const_mul (5 : ℂ)).deriv
  rw [hd] at h
  have hr := (abs_le.mp ((Complex.abs_re_le_norm (deriv f z - 5)).trans h)).1
  norm_num at hr
  linarith

theorem exists_bilipschitz_inset_extension {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f sourceStrips)
    (hclose : ∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100) (j : ℕ) :
    ∃ H : ℂ ≃ₜ ℂ, EqOn f H (insetSourceStrip j) ∧ ∃ L L' : ℝ≥0,
      LipschitzWith L H ∧ LipschitzWith L' H.symm := by
  let l := (height j - 3 / 5) / 4
  let u := (height j + 13 / 5) / 4
  have heq : insetSourceStrip j = closedHorizontalStrip l u := by
    ext z
    change (height j - 3 / 5 ≤ 4 * z.im ∧ 4 * z.im ≤ height j + 13 / 5) ↔
      l ≤ z.im ∧ z.im ≤ u
    dsimp [l, u]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  rw [heq]
  apply exists_bilipschitz_extension_on_horizontalStrip (by dsimp [l, u]; linarith)
    (m := 2) (M := 8) ?_ (by norm_num)
  · intro z hz
    have hz' : z ∈ insetSourceStrip j := heq.symm ▸ hz
    exact ⟨re_deriv_lower_bound_on_inset hf hclose hz', (derivative_bounds_on_inset hf hclose hz').2⟩
  · intro z hz
    have hz' : z ∈ insetSourceStrip j := heq.symm ▸ hz
    exact hf.differentiableAt (Filter.mem_of_superset
      ((isOpen_sourceStrip j).mem_nhds (insetSourceStrip_subset j hz')) (subset_iUnion _ j))

end EremenkosConjecture.Scaffolding
