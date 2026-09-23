import EremenkosConjecture.FilledAttachmentConvergence
import FunctionTheory.Conformal.HalfStripEndpoint
import FunctionTheory.Conformal.ThinAttachmentEscape

open Set Metric Complex Filter Function FunctionTheory
open scoped Topology

namespace EremenkosConjecture

/-- The narrowing-channel estimate applied to the actual filled domains:
the entire attached side moves uniformly left under the end-normalized strip
maps. Both the maps and their convergence are constructed from the geometry. -/
theorem exists_filled_attachment_maps_with_uniform_left_escape
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
      TendstoLocallyUniformlyOn G g atTop V ∧
      ∀ M : ℝ, ∀ᶠ n in atTop, ∀ x ∈ U n, x.re < a →
        (discToHorizontalStrip (G n x)).re < M := by
  let U := fun n => filledAttachmentDomain (C n) (ζ : ℂ) (a : ℂ) (s n) (η n) (Real.pi / 2)
  let V := {z : ℂ | a < z.re ∧ |z.im| < Real.pi / 2}
  obtain ⟨G, g, hG, hg, hconv⟩ := exists_convergent_right_end_maps_for_filled_attachments
    hCc hCi hζ hCdec hsdec hηdec hs hη hηH hmax hAa hCim hηlim
  have hH : 0 < Real.pi / 2 := half_pos Real.pi_pos
  have hprops n := filledAttachmentDomain_properties (X := ∅) (a := (a : ℂ))
    (hCi n) (hζ n) (empty_subset _) (hs n) (hη n) hH (by simp) (hmax n) hAa
  let J := fun n => invFunOn (G n) (U n)
  have hJd n : DifferentiableOn ℂ (J n) (ball 0 1) := by
    have h := DifferentiableOn.invFunOn (hG n).differentiableOn (hprops n).1 (hG n).bijOn.injOn
    rwa [(hG n).bijOn.image_eq] at h
  have hJU n : MapsTo (J n) (ball 0 1) (U n) :=
    (hG n).bijOn.surjOn.mapsTo_invFunOn
  have hJ0 n : J n 0 = ((a + 1 : ℝ) : ℂ) := by
    simpa only [(hG n).map_base] using
      (hG n).bijOn.injOn.leftInvOn_invFunOn (hG n).base_mem
  let R₀ := min (Real.pi / 2) 1
  have hR₀ : 0 < R₀ := lt_min hH zero_lt_one
  have hfar : R₀ ≤ dist (((a + 1 : ℝ) : ℂ)) (a : ℂ) := by
    simpa [R₀, dist_eq_norm, ← ofReal_sub] using min_le_right (Real.pi / 2) (1 : ℝ)
  have hgate : ∀ r > 0, ∀ᶠ n in atTop,
      ∀ w ∈ U n, w.re = (a : ℂ).re → dist w (a : ℂ) ≤ r := by
    intro r hr
    filter_upwards [hηlim.eventually (gt_mem_nhds hr)] with n hn
    exact fun w hw he => ((hprops n).2.2.2.1 w hw he).trans hn.le
  have hrad : ∀ t ∈ Ioo 0 R₀, (a : ℂ) + (t : ℂ) ∈ V := by
    intro t ht
    exact ⟨by simpa using lt_add_of_pos_right a ht.1, by simpa using hH⟩
  have hend : Tendsto (fun t : ℝ => g ((a : ℂ) + (t : ℂ))) (𝓝[>] 0) (𝓝 (-1)) := by
    simpa only [ofReal_add] using rightEndRiemannMap_halfstrip_left_limit hg
  refine ⟨G, g, hG, hg, hconv, ?_⟩
  exact uniform_left_escape_of_shrinking_attachment
    (fun n => (hprops n).1) (fun n => (hG n).differentiableOn)
    (fun n => (hG n).bijOn.injOn) (fun n => (hG n).bijOn.mapsTo)
    (fun n => (hJd n).continuousOn) hJU
    (fun n => (hG n).bijOn.invOn_invFunOn.2)
    (fun n => (hG n).bijOn.invOn_invFunOn.1) hJ0 hR₀ (by simp) hfar
    (fun n ρ hρ θ hθ => (hprops n).2.2.2.2 ρ
      ⟨hρ.1, hρ.2.trans_le (min_le_left _ _)⟩ θ hθ)
    hgate hconv hrad hend

end EremenkosConjecture
