import EremenkosConjecture.FilledAttachmentKernel
import FunctionTheory.Conformal.RightEndKernel
import Mathlib.Analysis.Convex.Contractible

open Set Metric Complex Filter FunctionTheory
open scoped Topology

namespace EremenkosConjecture

theorem filledAttachmentDomain_im_bound
    {C : Set ℂ} {ζ a : ℂ} {s η H : ℝ}
    (hCim : ∀ z ∈ C, |z.im - a.im| ≤ H)
    (hη : η ≤ H) (him : ζ.im = a.im) :
    ∀ z ∈ filledAttachmentDomain C ζ a s η H, |z.im - a.im| < H := by
  apply strict_im_bound_of_open isOpen_interior.connectedComponentIn
  intro z hz
  apply ComplexApproximation.fill_preserves_im_bound (E := attachedHalfStrips C ζ a s η H)
    (fun w hw => ?_) z (interior_subset (connectedComponentIn_subset _ _ hz))
  rcases hw with (hw | hw) | hw
  · exact hCim w hw
  · exact (by simpa only [him] using hw.2 : |w.im - a.im| ≤ η).trans hη
  · exact hw.2

/-- The actual filled attachment domains admit disk maps normalized at a
fixed point in the wide halfstrip and at the right end. These maps converge
locally uniformly on that halfstrip when the channel shrinks. -/
theorem exists_convergent_right_end_maps_for_filled_attachments
    {C : ℕ → Set ℂ} {s η : ℕ → ℝ} {ζ a A : ℝ}
    (hCc : ∀ n, IsCompact (C n)) (hCi : ∀ n, IsConnected (interior (C n)))
    (hζ : ∀ n, (ζ : ℂ) ∈ interior (C n))
    (hCdec : Antitone C) (hsdec : Antitone s) (hηdec : Antitone η)
    (hs : ∀ n, 0 < s n) (hη : ∀ n, 0 < η n) (hηH : ∀ n, η n ≤ Real.pi / 2)
    (hmax : ∀ n, ∀ z ∈ C n, z.re ≤ A) (hAa : A < a)
    (hCim : ∀ n, ∀ z ∈ C n, |z.im| ≤ Real.pi / 2)
    (hηlim : Tendsto η atTop (𝓝 0)) :
    let U := fun n => filledAttachmentDomain (C n) (ζ : ℂ) (a : ℂ) (s n) (η n) (Real.pi / 2)
    let V := {z : ℂ | a < z.re ∧ |z.im| < Real.pi / 2}
    ∃ (G : ℕ → ℂ → ℂ) (g : ℂ → ℂ),
      (∀ n, IsRightEndRiemannMapOn (G n) (U n) ((a + 1 : ℝ) : ℂ)) ∧
      IsRightEndRiemannMapOn g V ((a + 1 : ℝ) : ℂ) ∧
      TendstoLocallyUniformlyOn G g atTop V := by
  let U := fun n => filledAttachmentDomain (C n) (ζ : ℂ) (a : ℂ) (s n) (η n) (Real.pi / 2)
  let V := {z : ℂ | a < z.re ∧ |z.im| < Real.pi / 2}
  have hH : 0 < Real.pi / 2 := half_pos Real.pi_pos
  have hprops n := filledAttachmentDomain_properties (X := ∅) (a := (a : ℂ))
    (hCi n) (hζ n) (empty_subset _) (hs n) (hη n) hH (by simp)
    (hmax n) hAa
  have hUo n : IsOpen (U n) := (hprops n).1
  have hUc n : IsSimplyConnected (U n) := (hprops n).2.1
  have hUS n : U n ⊆ standardHorizontalStrip := by
    intro z hz
    change |z.im| < Real.pi / 2
    simpa only [ofReal_im, sub_zero] using
      filledAttachmentDomain_im_bound
        (fun w hw => by simpa only [ofReal_im, sub_zero] using hCim n w hw)
        (hηH n) (by simp) z hz
  have hVU n : V ⊆ U n := by
    simpa only [ofReal_re, ofReal_im, sub_zero] using
      straight_tail_subset_filledAttachmentDomain (a := (a : ℂ))
        (hCi n) (hζ n) (hs n) (hη n) hH (by simp)
  have hdec : Antitone U := fun i j hij =>
    filledAttachmentDomain_mono (hCdec hij) (hsdec hij) (hηdec hij)
  have hVo : IsOpen V := by
    simpa only [ofReal_re, ofReal_im, sub_zero] using isOpen_right_halfstrip (a : ℂ) (Real.pi / 2)
  have hVconv : Convex ℝ V := by
    simpa only [ofReal_re, ofReal_im, sub_zero] using convex_right_halfstrip (a : ℂ) (Real.pi / 2)
  have hz₀ : ((a + 1 : ℝ) : ℂ) ∈ V := ⟨by simp, by simpa using hH⟩
  have hVc : IsSimplyConnected V := by
    letI : ContractibleSpace V := hVconv.contractibleSpace ⟨_, hz₀⟩
    change SimplyConnectedSpace V
    exact inferInstance
  have hVS : V ⊆ standardHorizontalStrip := fun _ hz => hz.2
  have htail : ∀ z ∈ standardHorizontalStrip, a < z.re → z ∈ V := fun _ hz hr => ⟨hr, hz⟩
  have hk : connectedComponentIn (interior (⋂ n, closure (U n))) ((a + 1 : ℝ) : ℂ) ⊆ V := by
    have he := filledAttachmentDomain_kernel_eq_right_halfstrip (a := (a : ℂ))
      hCc hCi hζ hs hη hηH hH (by simp) hmax hAa
      (fun n z hz => by simpa only [ofReal_im, sub_zero] using hCim n z hz) hηlim
      (show (a : ℂ).re < ((a + 1 : ℝ) : ℂ).re ∧
          |((a + 1 : ℝ) : ℂ).im - (a : ℂ).im| < Real.pi / 2 by
        simpa only [V, mem_setOf_eq, ofReal_re, ofReal_im, sub_zero] using hz₀)
    simpa only [ofReal_re, ofReal_im, sub_zero] using he.subset
  choose G hG using fun n => exists_rightEndRiemannMapOn
    (hUo n) (hUc n) (hUS n) (fun z hz hr => hVU n (htail z hz hr)) (hVU n hz₀)
  obtain ⟨g, hg⟩ := exists_rightEndRiemannMapOn hVo hVc hVS htail hz₀
  exact ⟨G, g, hG, hg, rightEndRiemannMaps_tendsto_on_kernel
    hUo hUc hUS hdec hVo hVc hVS hVU htail hk hG hg⟩

end EremenkosConjecture
