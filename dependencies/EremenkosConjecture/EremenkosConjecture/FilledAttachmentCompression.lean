import EremenkosConjecture.FilledAttachmentEscape
import FunctionTheory.Conformal.CompactCompression

open Set Metric Complex Filter FunctionTheory
open scoped Topology

namespace EremenkosConjecture

/-- One actual attachment domain and one conformal map satisfy both controls
in the continuum construction: compression of a compact set on the ray side,
and uniformly large negative real parts on the whole attached set `X`. -/
theorem exists_filled_attachment_map_with_simultaneous_control
    {C : ℕ → Set ℂ} {s η : ℕ → ℝ} {X K : Set ℂ} {ζ a A r ε : ℝ}
    (hCc : ∀ n, IsCompact (C n)) (hCi : ∀ n, IsConnected (interior (C n)))
    (hζ : ∀ n, (ζ : ℂ) ∈ interior (C n)) (hXC : ∀ n, X ⊆ interior (C n))
    (hCdec : Antitone C) (hsdec : Antitone s) (hηdec : Antitone η)
    (hs : ∀ n, 0 < s n) (hη : ∀ n, 0 < η n) (hηH : ∀ n, η n ≤ Real.pi / 2)
    (hmax : ∀ n, ∀ z ∈ C n, z.re ≤ A) (hAa : A < a)
    (hCim : ∀ n, ∀ z ∈ C n, |z.im| ≤ Real.pi / 2)
    (hηlim : Tendsto η atTop (𝓝 0))
    (hK : IsCompact K) (hKV : K ⊆ {z : ℂ | a < z.re ∧ |z.im| < Real.pi / 2})
    (hr : 0 < r) (hε : 0 < ε) (M : ℝ) :
    let U := fun n => filledAttachmentDomain (C n) (ζ : ℂ) (a : ℂ) (s n) (η n) (Real.pi / 2)
    ∃ (n : ℕ) (c : ℝ) (F : ℂ → ℂ),
      IsRightEndRiemannMapOn F (U n) ((a + 1 : ℝ) : ℂ) ∧
      0 < c ∧ c * (Real.pi / 2) < r ∧
      (∀ z ∈ K, ‖(c : ℂ) * discToHorizontalStrip (F z)‖ < ε) ∧
      ∀ x ∈ X, ((c : ℂ) * discToHorizontalStrip (F x)).re < M := by
  let U := fun n => filledAttachmentDomain (C n) (ζ : ℂ) (a : ℂ) (s n) (η n) (Real.pi / 2)
  let V := {z : ℂ | a < z.re ∧ |z.im| < Real.pi / 2}
  obtain ⟨G, g, hG, hg, hconv, hleft⟩ :=
    exists_filled_attachment_maps_with_uniform_left_escape
      hCc hCi hζ hCdec hsdec hηdec hs hη hηH hmax hAa hCim hηlim
  have hH : 0 < Real.pi / 2 := half_pos Real.pi_pos
  have hVU n : V ⊆ U n := by
    simpa only [ofReal_re, ofReal_im, sub_zero] using
      straight_tail_subset_filledAttachmentDomain (a := (a : ℂ))
        (hCi n) (hζ n) (hs n) (hη n) hH (by simp)
  have hXU n : X ⊆ U n := by
    have h := filledAttachmentDomain_properties (a := (a : ℂ))
      (hCi n) (hζ n) (hXC n) (hs n) (hη n) hH (by simp) (hmax n) hAa
    exact fun x hx => h.2.2.1 (Or.inl hx)
  have hXleft : ∀ x ∈ X, x.re < a :=
    fun x hx => (hmax 0 x (interior_subset (hXC 0 hx))).trans_lt hAa
  have hstripconv := locallyUniform_discToHorizontalStrip hconv hg.differentiableOn.continuousOn
    (fun n => (hG n).bijOn.mapsTo.mono_left (hVU n)) hg.bijOn.mapsTo
  have hstripcont : ContinuousOn (fun z => discToHorizontalStrip (g z)) V :=
    differentiableOn_discToHorizontalStrip.continuousOn.comp
      hg.differentiableOn.continuousOn hg.bijOn.mapsTo
  have hleftX : ∀ B : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ X, (discToHorizontalStrip (G n x)).re < B := by
    intro B
    filter_upwards [hleft B] with n hn
    exact fun x hx => hn x (hXU n hx) (hXleft x hx)
  obtain ⟨c, n, hc, hcr, hKbound, hXbound⟩ :=
    exists_scaled_map_with_compact_control_and_left_escape
      hstripconv hstripcont hK hKV hr hε hleftX M
  exact ⟨n, c, G n, hG n, hc, hcr, hKbound, hXbound⟩

end EremenkosConjecture
