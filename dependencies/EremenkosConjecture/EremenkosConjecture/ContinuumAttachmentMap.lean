import EremenkosConjecture.NarrowAttachmentMap
import EremenkosConjecture.ComplexJordanNeighbourhood

open Set Metric Complex Filter FunctionTheory Asymptotics
open scoped Topology

namespace EremenkosConjecture

/-- A full compact continuum admits an actual attached strip domain and a
conformal map with both controls required in the recursive construction.
The compact decoration can be chosen in any prescribed open neighbourhood.
The map is normalized at a finite point and at the right end; its exponential
end estimates refer to this same map. -/
theorem exists_continuum_attachment_map
    {X K N : Set ℂ} {ζ a s κ r ε : ℝ}
    (hX : IsCompact X) (hconn : IsConnected X) (hfull : IsConnected Xᶜ)
    (hζ : (ζ : ℂ) ∈ X) (hmax : ∀ z ∈ X, z.re ≤ ζ)
    (hXS : X ⊆ standardHorizontalStrip) (hζa : ζ < a)
    (hN : IsOpen N) (hXN : X ⊆ N)
    (hs : 0 < s) (hκ : 0 < κ) (hκH : κ ≤ Real.pi / 2)
    (hK : IsCompact K) (hKV : K ⊆ {z : ℂ | a < z.re ∧ |z.im| < Real.pi / 2})
    (hr : 0 < r) (hε : 0 < ε) (M : ℝ) :
    ∃ (C : Set ℂ) (η c ρ : ℝ) (φ : ℂ → ℂ),
      let U := filledAttachmentDomain C (ζ : ℂ) (a : ℂ) s η (Real.pi / 2)
      IsCompact C ∧ IsConnected (interior C) ∧ X ⊆ interior C ∧ C ⊆ N ∧
      0 < η ∧ η ≤ κ ∧ IsOpen U ∧ IsSimplyConnected U ∧
      X ∪ horizontalRay (ζ : ℂ) ⊆ U ∧ U ⊆ standardHorizontalStrip ∧
      DifferentiableOn ℂ φ U ∧ BijOn φ U standardHorizontalStrip ∧
      φ ((a + 1 : ℝ) : ℂ) = 0 ∧
      (fun z => deriv φ z - 1) =O[comap Complex.re atTop ⊓ 𝓟 U]
        (fun z => Real.exp (-z.re)) ∧
      (fun z => φ z - (z + (ρ : ℂ))) =O[comap Complex.re atTop ⊓ 𝓟 U]
        (fun z => Real.exp (-z.re)) ∧
      0 < c ∧ c * (Real.pi / 2) < r ∧
      (∀ z ∈ K, ‖(c : ℂ) * φ z‖ < ε) ∧
      ∀ x ∈ X, ((c : ℂ) * φ x).re < M := by
  let A := (ζ + a) / 2
  have hζA : ζ < A := by dsimp [A]; linarith
  have hAa : A < a := by dsimp [A]; linarith
  let W := N ∩ ({z : ℂ | z.re < A} ∩ standardHorizontalStrip)
  have hWo : IsOpen W := hN.inter
    ((isOpen_lt continuous_re continuous_const).inter isOpen_standardHorizontalStrip)
  have hXW : X ⊆ W := fun z hz => ⟨hXN hz, (hmax z hz).trans_lt hζA, hXS hz⟩
  obtain ⟨C, hCc, _, _, hXC, hCW, _, hCi, _⟩ :=
    exists_jordan_compact_neighbourhood X W hX hconn hfull hWo hXW
  have hCre : ∀ z ∈ C, z.re ≤ A := fun z hz => (hCW hz).2.1.le
  have hCim : ∀ z ∈ C, |z.im| ≤ Real.pi / 2 := fun z hz => (hCW hz).2.2.le
  obtain ⟨η, c, F, hη, hηκ, hF, hc, hcr, hFK, hFX⟩ :=
    exists_narrow_attachment_map_with_simultaneous_control
      hCc hCi (hXC hζ) hXC hs hκ hκH hCre hAa hCim hK hKV hr hε M
  let U := filledAttachmentDomain C (ζ : ℂ) (a : ℂ) s η (Real.pi / 2)
  have hp := filledAttachmentDomain_properties (a := (a : ℂ)) hCi (hXC hζ) hXC
    hs hη (half_pos Real.pi_pos) (by simp) hCre (by simpa using hAa)
  have hUS : U ⊆ standardHorizontalStrip := by
    intro z hz
    change |z.im| < Real.pi / 2
    simpa only [ofReal_im, sub_zero] using
      filledAttachmentDomain_im_bound (a := (a : ℂ))
        (by simpa only [ofReal_im, sub_zero] using hCim)
        (hηκ.trans hκH) (by simp) z hz
  have htail : ∀ z ∈ standardHorizontalStrip, a < z.re → z ∈ U := by
    intro z hz hrz
    change |z.im| < Real.pi / 2 at hz
    exact straight_tail_subset_filledAttachmentDomain (a := (a : ℂ)) hCi (hXC hζ)
      hs hη (half_pos Real.pi_pos) (by simp) ⟨by simpa using hrz, by simpa using hz⟩
  obtain ⟨hd, hb, h0, ρ, hOd, hOv, _⟩ := hF.strip_end_estimates hp.1 hUS htail
  exact ⟨C, η, c, ρ, fun z => discToHorizontalStrip (F z),
    hCc, hCi, hXC, fun z hz => (hCW hz).1, hη, hηκ,
    hp.1, hp.2.1, hp.2.2.1, hUS, hd, hb, h0, hOd, hOv, hc, hcr, hFK, hFX⟩

end EremenkosConjecture
