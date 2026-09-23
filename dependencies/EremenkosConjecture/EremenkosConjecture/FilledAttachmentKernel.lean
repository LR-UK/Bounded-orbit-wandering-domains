import EremenkosConjecture.FilledAttachmentBounds
import FunctionTheory.Conformal.ShrinkingGateKernel

open Set Metric Complex Filter
open scoped Topology

namespace EremenkosConjecture

theorem isOpen_right_halfstrip (a : ℂ) (H : ℝ) :
    IsOpen {z : ℂ | a.re < z.re ∧ |z.im - a.im| < H} :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt (Complex.continuous_im.sub continuous_const).abs continuous_const)

theorem convex_right_halfstrip (a : ℂ) (H : ℝ) :
    Convex ℝ {z : ℂ | a.re < z.re ∧ |z.im - a.im| < H} := by
  have he : {z : ℂ | a.re < z.re ∧ |z.im - a.im| < H} =
      {z : ℂ | a.re < z.re} ∩
        ({z : ℂ | a.im - H < z.im} ∩ {z : ℂ | z.im < a.im + H}) := by
    ext z
    simp only [mem_setOf_eq, mem_inter_iff, abs_lt]
    constructor <;> rintro ⟨hr, hl, hu⟩ <;> exact ⟨hr, by linarith, by linarith⟩
  rw [he]
  exact (convex_halfSpace_re_gt _).inter
    ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _))

/-- The kernel seen from the right-hand base point is exactly the fixed
straight halfstrip when the connecting channel shrinks to zero width.
No empty-interior assumption on the left decoration is made. -/
theorem filledAttachmentDomain_kernel_eq_right_halfstrip
    {C : ℕ → Set ℂ} {s η : ℕ → ℝ} {ζ a z₀ : ℂ} {H A : ℝ}
    (hCc : ∀ n, IsCompact (C n)) (hCi : ∀ n, IsConnected (interior (C n)))
    (hζ : ∀ n, ζ ∈ interior (C n)) (hs : ∀ n, 0 < s n) (hη : ∀ n, 0 < η n)
    (hηH : ∀ n, η n ≤ H) (hH : 0 < H) (him : ζ.im = a.im)
    (hmax : ∀ n, ∀ z ∈ C n, z.re ≤ A) (hAa : A < a.re)
    (hCim : ∀ n, ∀ z ∈ C n, |z.im - a.im| ≤ H)
    (hηlim : Tendsto η atTop (𝓝 0))
    (hz₀ : a.re < z₀.re ∧ |z₀.im - a.im| < H) :
    connectedComponentIn
      (interior (⋂ n, closure (filledAttachmentDomain (C n) ζ a (s n) (η n) H))) z₀ =
      {z : ℂ | a.re < z.re ∧ |z.im - a.im| < H} := by
  let U := fun n => filledAttachmentDomain (C n) ζ a (s n) (η n) H
  let W := interior (⋂ n, closure (U n))
  let V : Set ℂ := {z : ℂ | a.re < z.re ∧ |z.im - a.im| < H}
  have hVU : ∀ n, V ⊆ U n := fun n =>
    straight_tail_subset_filledAttachmentDomain (hCi n) (hζ n) (hs n) (hη n) hH him
  have hVW : V ⊆ W := by
    apply interior_maximal _ (isOpen_right_halfstrip a H)
    intro z hz
    exact mem_iInter.mpr (fun n => subset_closure (hVU n hz))
  have hclosed (n : ℕ) : IsClosed (ComplexApproximation.fill
      (attachedHalfStrips (C n) ζ a (s n) (η n) H)) :=
    ComplexApproximation.isClosed_fill
      (((hCc n).isClosed.union (isClosed_closedHalfStrip ζ (s n) (η n))).union
        (isClosed_closedHalfStrip a 0 H))
  have hcl (n : ℕ) : closure (U n) ⊆ ComplexApproximation.fill
      (attachedHalfStrips (C n) ζ a (s n) (η n) H) :=
    (hclosed n).closure_subset_iff.mpr ((connectedComponentIn_subset _ _).trans interior_subset)
  have hgate : ∀ r > 0, ∀ᶠ n in atTop,
      ∀ z ∈ interior (closure (U n)), z.re = a.re → dist z a ≤ r := by
    intro r hr
    filter_upwards [hηlim.eventually (gt_mem_nhds hr)] with n hn
    intro z hz hza
    exact (interior_filled_attachment_gate_bound (hmax n) hAa him z
      (interior_mono (hcl n) hz) hza).trans hn.le
  have hright := FunctionTheory.kernel_component_right_of_shrinking_gate (hVW hz₀) hz₀.1 hgate
  have hWheight : ∀ z ∈ W, |z.im - a.im| < H := by
    apply strict_im_bound_of_open isOpen_interior
    intro z hz
    apply ComplexApproximation.fill_preserves_im_bound (E := attachedHalfStrips (C 0) ζ a (s 0) (η 0) H)
      (fun w hw => ?_) z (hcl 0 (mem_iInter.mp (interior_subset hz) 0))
    rcases hw with (hw | hw) | hw
    · exact hCim 0 w hw
    · exact (by simpa only [him] using hw.2 : |w.im - a.im| ≤ η 0).trans (hηH 0)
    · exact hw.2
  apply subset_antisymm
  · intro z hz
    exact ⟨hright hz, hWheight z (connectedComponentIn_subset W z₀ hz)⟩
  · exact (convex_right_halfstrip a H).isPreconnected.subset_connectedComponentIn hz₀ hVW

end EremenkosConjecture
