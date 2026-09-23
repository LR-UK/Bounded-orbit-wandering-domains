import EremenkosConjecture.FilledAttachmentCompression
import Mathlib.Analysis.SpecificLimits.Basic

open Set Metric Complex Filter FunctionTheory
open scoped Topology

namespace EremenkosConjecture

/-- For a fixed compact decoration, an arbitrarily narrow channel gives a
conformal map with simultaneous compact compression and uniform left escape.
No family of domains or convergence data is assumed in this statement. -/
theorem exists_narrow_attachment_map_with_simultaneous_control
    {C X K : Set ℂ} {ζ a A s κ r ε : ℝ}
    (hCc : IsCompact C) (hCi : IsConnected (interior C))
    (hζ : (ζ : ℂ) ∈ interior C) (hXC : X ⊆ interior C)
    (hs : 0 < s) (hκ : 0 < κ) (hκH : κ ≤ Real.pi / 2)
    (hmax : ∀ z ∈ C, z.re ≤ A) (hAa : A < a)
    (hCim : ∀ z ∈ C, |z.im| ≤ Real.pi / 2)
    (hK : IsCompact K) (hKV : K ⊆ {z : ℂ | a < z.re ∧ |z.im| < Real.pi / 2})
    (hr : 0 < r) (hε : 0 < ε) (M : ℝ) :
    ∃ (η c : ℝ) (F : ℂ → ℂ), 0 < η ∧ η ≤ κ ∧
      IsRightEndRiemannMapOn F
        (filledAttachmentDomain C (ζ : ℂ) (a : ℂ) s η (Real.pi / 2)) ((a + 1 : ℝ) : ℂ) ∧
      0 < c ∧ c * (Real.pi / 2) < r ∧
      (∀ z ∈ K, ‖(c : ℂ) * discToHorizontalStrip (F z)‖ < ε) ∧
      ∀ x ∈ X, ((c : ℂ) * discToHorizontalStrip (F x)).re < M := by
  let η : ℕ → ℝ := fun n => κ / ((n : ℝ) + 1)
  have hη n : 0 < η n := div_pos hκ (by positivity)
  have hηκ n : η n ≤ κ := by
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hηdec : Antitone η := by
    intro i j hij
    exact div_le_div_of_nonneg_left hκ.le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hηlim : Tendsto η atTop (𝓝 0) := by
    simpa only [η, mul_zero, mul_one_div] using
      tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  obtain ⟨n, c, F, hF, hc, hcr, hFK, hFX⟩ :=
    exists_filled_attachment_map_with_simultaneous_control
      (C := fun _ => C) (s := fun _ => s) (η := η)
      (fun _ => hCc) (fun _ => hCi) (fun _ => hζ) (fun _ => hXC)
      (fun _ _ _ => Subset.rfl) (fun _ _ _ => le_rfl) hηdec
      (fun _ => hs) hη (fun n => (hηκ n).trans hκH)
      (fun _ => hmax) hAa (fun _ => hCim) hηlim hK hKV hr hε M
  exact ⟨η n, c, F, hη n, hηκ n, hF, hc, hcr, hFK, hFX⟩

end EremenkosConjecture
