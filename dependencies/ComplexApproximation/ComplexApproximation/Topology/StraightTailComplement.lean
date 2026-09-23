import ComplexApproximation.Topology.NestedBandNonseparation
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Module.Connected

open Set Metric Complex Bornology

namespace ComplexApproximation

/-- A filled set bounded to the left and in height, with just one straight
halfstrip at its right end, has connected plane complement. -/
theorem isConnected_compl_of_straight_tail {E : Set ℂ} {L A c H η : ℝ}
    (hfull : NoBoundedComplementComponents E)
    (hleft : ∀ z ∈ E, L ≤ z.re) (him : ∀ z ∈ E, |z.im - c| ≤ H)
    (hηH : η ≤ H)
    (htail : ∀ z : ℂ, A < z.re → (z ∈ E ↔ |z.im - c| ≤ η)) :
    IsConnected Eᶜ := by
  let P := {z : ℂ | z.re < L}
  let T := {z : ℂ | c + H < z.im}
  let D := {z : ℂ | z.im < c - H}
  let T' := {z : ℂ | A < z.re ∧ c + η < z.im}
  let D' := {z : ℂ | A < z.re ∧ z.im < c - η}
  let Q := (P ∪ (T ∪ T')) ∪ (D ∪ D')
  have hP : IsConnected P := (convex_halfSpace_re_lt L).isConnected
    ⟨⟨L - 1, c⟩, by dsimp; linarith⟩
  have hT : IsConnected T := (convex_halfSpace_im_gt (c + H)).isConnected
    ⟨⟨A + 1, c + H + 1⟩, by dsimp; linarith⟩
  have hD : IsConnected D := (convex_halfSpace_im_lt (c - H)).isConnected
    ⟨⟨A + 1, c - H - 1⟩, by dsimp; linarith⟩
  have hT' : IsConnected T' := ((convex_halfSpace_re_gt A).inter
    (convex_halfSpace_im_gt (c + η))).isConnected
      ⟨⟨A + 1, c + H + 1⟩, by change A < A + 1 ∧ c + η < c + H + 1; constructor <;> linarith⟩
  have hD' : IsConnected D' := ((convex_halfSpace_re_gt A).inter
    (convex_halfSpace_im_lt (c - η))).isConnected
      ⟨⟨A + 1, c - H - 1⟩, by change A < A + 1 ∧ c - H - 1 < c - η; constructor <;> linarith⟩
  have hTT : IsConnected (T ∪ T') := hT.union
    ⟨⟨A + 1, c + H + 1⟩, by change c + H < c + H + 1; linarith,
      by change A < A + 1 ∧ c + η < c + H + 1; constructor <;> linarith⟩ hT'
  have hDD : IsConnected (D ∪ D') := hD.union
    ⟨⟨A + 1, c - H - 1⟩, by change c - H - 1 < c - H; linarith,
      by change A < A + 1 ∧ c - H - 1 < c - η; constructor <;> linarith⟩ hD'
  have hPT : IsConnected (P ∪ (T ∪ T')) := hP.union
    ⟨⟨L - 1, c + H + 1⟩, by dsimp [P]; linarith, Or.inl (by dsimp [T]; linarith)⟩ hTT
  have hQ : IsConnected Q := hPT.union
    ⟨⟨L - 1, c - H - 1⟩, Or.inl (by dsimp [P]; linarith),
      Or.inl (by dsimp [D]; linarith)⟩ hDD
  have hQE : Q ⊆ Eᶜ := by
    rintro z ((hz | (hz | hz)) | (hz | hz)) hzE
    · exact (not_lt_of_ge (hleft z hzE)) hz
    · have hi := (abs_le.mp (him z hzE)).2
      change c + H < z.im at hz
      linarith
    · have hi := (abs_le.mp ((htail z hz.1).mp hzE)).2
      linarith [hz.2]
    · have hi := (abs_le.mp (him z hzE)).1
      change z.im < c - H at hz
      linarith
    · have hi := (abs_le.mp ((htail z hz.1).mp hzE)).1
      linarith [hz.2]
  have hbounded : IsBounded (Eᶜ \ Q) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨|L| + |A| + H + |c|, ?_⟩
    intro z hz
    have hLz : L ≤ z.re := le_of_not_gt (fun h => hz.2 (Or.inl (Or.inl h)))
    have hzimhi : z.im ≤ c + H := le_of_not_gt (fun h => hz.2 (Or.inl (Or.inr (Or.inl h))))
    have hzimlo : c - H ≤ z.im := le_of_not_gt (fun h => hz.2 (Or.inr (Or.inl h)))
    have hzA : z.re ≤ A := by
      by_contra hn
      have hAz := lt_of_not_ge hn
      have hi : z.im ≤ c + η := le_of_not_gt (fun h => hz.2 (Or.inl (Or.inr (Or.inr ⟨hAz, h⟩))))
      have hl : c - η ≤ z.im := le_of_not_gt (fun h => hz.2 (Or.inr (Or.inr ⟨hAz, h⟩)))
      exact hz.1 ((htail z hAz).mpr (abs_le.mpr ⟨by linarith, by linarith⟩))
    have hre : |z.re| ≤ |L| + |A| := abs_le.mpr
      ⟨by linarith [neg_abs_le L, abs_nonneg A], by linarith [le_abs_self A, abs_nonneg L]⟩
    have hi : |z.im| ≤ H + |c| := abs_le.mpr
      ⟨by linarith [neg_abs_le c], by linarith [le_abs_self c]⟩
    exact (norm_le_abs_re_add_abs_im z).trans (by linarith)
  exact isConnected_of_unbounded_components_of_connected_subset hQ hQE hbounded hfull

end ComplexApproximation
