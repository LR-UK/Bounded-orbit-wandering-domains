import EremenkosConjecture.FilledRayInsets
import ComplexApproximation.Topology.StraightTailComplement

open Set Metric Complex

namespace EremenkosConjecture

/-- Global coordinate bounds and an exact straight tail for a filled compact
decoration and halfstrip. -/
theorem exists_filledRayInset_bounds {C : Set ℂ} {ζ : ℂ} {s η : ℝ}
    (hC : IsCompact C) (hs : 0 ≤ s) :
    ∃ L H A : ℝ, η ≤ H ∧ ζ.re ≤ A ∧
      (∀ z ∈ filledRayInset C ζ s η, L ≤ z.re ∧ |z.im - ζ.im| ≤ H) ∧
      ∀ z : ℂ, A < z.re → (z ∈ filledRayInset C ζ s η ↔ |z.im - ζ.im| ≤ η) := by
  obtain ⟨B, hB, hnorm⟩ := hC.isBounded.exists_pos_norm_le
  let L := min (-B) (ζ.re - s)
  let H := max (B + |ζ.im|) η
  let A := max B ζ.re
  have hCre : ∀ z ∈ C, L ≤ z.re := by
    intro z hz
    exact (min_le_left _ _).trans ((abs_le.mp ((abs_re_le_norm z).trans (hnorm z hz))).1)
  have hCim : ∀ z ∈ C, |z.im - ζ.im| ≤ H := by
    intro z hz
    apply (abs_sub _ _).trans
    have hi := (abs_im_le_norm z).trans (hnorm z hz)
    dsimp [H]
    linarith [le_max_left (B + |ζ.im|) η]
  have hbounds := filledRayInset_coordinate_bounds (ζ := ζ) (s := s) (η := η)
    hCre hCim (min_le_right _ _) (le_max_right _ _)
  refine ⟨L, H, A, le_max_right _ _, le_max_right _ _, hbounds, ?_⟩
  intro z hz
  apply filledRayInset_tail_iff (fun w hw => (re_le_norm w).trans (hnorm w hw))
    ((le_max_left B ζ.re).trans_lt hz)
  have : ζ.re ≤ A := le_max_right _ _
  linarith

/-- The complement of a compact decoration with a filled halfstrip is
connected. This is the nonseparation input for the approximation band. -/
theorem isConnected_compl_filledRayInset {C : Set ℂ} {ζ : ℂ} {s η : ℝ}
    (hC : IsCompact C) (hs : 0 ≤ s) :
    IsConnected (filledRayInset C ζ s η)ᶜ := by
  obtain ⟨L, H, A, hηH, _, hbounds, htail⟩ := exists_filledRayInset_bounds (ζ := ζ) (η := η) hC hs
  exact ComplexApproximation.isConnected_compl_of_straight_tail
    (ComplexApproximation.noBoundedComplementComponents_fill _)
    (fun z hz => (hbounds z hz).1) (fun z hz => (hbounds z hz).2) hηH htail

end EremenkosConjecture
