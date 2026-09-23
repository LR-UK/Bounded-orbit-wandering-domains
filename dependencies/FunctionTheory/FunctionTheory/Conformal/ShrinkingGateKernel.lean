import FunctionTheory.Conformal.HalfPlaneKernel

open Set Metric Complex Filter
open scoped Topology

namespace FunctionTheory

theorem open_set_avoids_vertical_line_of_singleton_intersection
    {W : Set ℂ} {a : ℂ} (hW : IsOpen W)
    (hgate : ∀ z ∈ W, z.re = a.re → z = a) :
    ∀ z ∈ W, z.re ≠ a.re := by
  intro z hz hre
  have hza := hgate z hz hre
  subst z
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW a hz
  let w := a + ((ε / 2 : ℝ) : ℂ) * I
  have hw : w ∈ W := by
    apply hball
    simpa [w, mem_ball, dist_eq_norm, abs_of_pos hε] using half_lt_self hε
  have hwre : w.re = a.re := by simp [w]
  have he := congrArg Complex.im (hgate w hw hwre)
  simp only [w, add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im,
    I_re, mul_zero, add_zero] at he
  linarith

theorem preconnected_subset_right_of_avoiding_vertical_line
    {S : Set ℂ} {a z₀ : ℂ} (hS : IsPreconnected S) (hz₀ : z₀ ∈ S)
    (hright : a.re < z₀.re) (hline : ∀ z ∈ S, z.re ≠ a.re) :
    S ⊆ {z : ℂ | a.re < z.re} := by
  apply hS.subset_right_of_subset_union
    (isOpen_lt Complex.continuous_re continuous_const)
    (isOpen_lt continuous_const Complex.continuous_re)
  · apply disjoint_left.mpr
    intro z hleft hright
    exact lt_asymm (show z.re < a.re from hleft) (show a.re < z.re from hright)
  · intro z hz
    exact lt_or_gt_of_ne (hline z hz)
  · exact ⟨z₀, hz₀, hright⟩

/-- When a vertical gate shrinks to a point, that point cannot belong to
the open kernel. The component seen from a base point on the right remains
entirely on the right. The left decoration may itself have interior. -/
theorem kernel_component_right_of_shrinking_gate
    {U : ℕ → Set ℂ} {a z₀ : ℂ}
    (hz₀ : z₀ ∈ interior (⋂ n, closure (U n))) (hright : a.re < z₀.re)
    (hgate : ∀ r > 0, ∀ᶠ n in atTop,
      ∀ z ∈ interior (closure (U n)), z.re = a.re → dist z a ≤ r) :
    connectedComponentIn (interior (⋂ n, closure (U n))) z₀ ⊆ {z : ℂ | a.re < z.re} := by
  let W := interior (⋂ n, closure (U n))
  have hgateW : ∀ z ∈ W, z.re = a.re → z = a := by
    intro z hz hre
    by_contra hne
    have hd : 0 < dist z a := dist_pos.mpr hne
    obtain ⟨n, hn⟩ := (hgate (dist z a / 2) (half_pos hd)).exists
    have hzn : z ∈ interior (closure (U n)) :=
      interior_mono (iInter_subset (fun n => closure (U n)) n) hz
    have h := hn z hzn hre
    linarith
  have hline := open_set_avoids_vertical_line_of_singleton_intersection isOpen_interior hgateW
  exact preconnected_subset_right_of_avoiding_vertical_line
    isPreconnected_connectedComponentIn (mem_connectedComponentIn hz₀) hright
    (fun z hz => hline z (connectedComponentIn_subset W z₀ hz))

end FunctionTheory
