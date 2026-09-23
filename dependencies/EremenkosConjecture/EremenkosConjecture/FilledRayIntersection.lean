import EremenkosConjecture.FilledRayInsets
import ComplexApproximation.Topology.FillingDecreasingIntersection
import FunctionTheory.Conformal.StripBounds

open Set Metric Complex Filter Bornology
open scoped Topology

namespace EremenkosConjecture

/-- For nested compact decorations and shrinking halfstrips, filling leaves
the exact limiting continuum and ray unchanged. In particular it introduces
no extra points into the intersection of the closed barriers. -/
theorem iInter_filledRayInset_eq
    {C : ℕ → Set ℂ} {s η : ℕ → ℝ} {ζ : ℂ}
    (hC : ∀ n, IsCompact (C n)) (hCanti : Antitone C)
    (hsanti : Antitone s) (hηanti : Antitone η)
    (hs : ∀ n, 0 ≤ s n) (hη : ∀ n, 0 ≤ η n)
    (hs0 : Tendsto s atTop (𝓝 0)) (hη0 : Tendsto η atTop (𝓝 0))
    (hfull : ComplexApproximation.NoBoundedComplementComponents
      ((⋂ n, C n) ∪ horizontalRay ζ)) :
    (⋂ n, filledRayInset (C n) ζ (s n) (η n)) = (⋂ n, C n) ∪ horizontalRay ζ := by
  let E := fun n => C n ∪ closedHalfStrip ζ (s n) (η n)
  have hSanti : Antitone (fun n => closedHalfStrip ζ (s n) (η n)) := by
    intro i j hij z hz
    exact ⟨by linarith [hz.1, hsanti hij], hz.2.trans (hηanti hij)⟩
  have hEanti : Antitone E := fun i j hij => union_subset_union (hCanti hij) (hSanti hij)
  have hinter : (⋂ n, E n) = (⋂ n, C n) ∪ horizontalRay ζ := by
    change (⋂ n, C n ∪ closedHalfStrip ζ (s n) (η n)) = _
    rw [iInter_union_of_antitone hCanti hSanti, iInter_closedHalfStrip_eq_ray hs hη hs0 hη0]
  obtain ⟨B, hB, hnorm⟩ := (hC 0).isBounded.exists_pos_norm_le
  let L := min (-B) (ζ.re - s 0)
  let H := max (B + |ζ.im|) (η 0)
  let A := max B ζ.re
  have hCre : ∀ z ∈ C 0, L ≤ z.re := by
    intro z hz
    exact (min_le_left _ _).trans ((abs_le.mp ((abs_re_le_norm z).trans (hnorm z hz))).1)
  have hCim : ∀ z ∈ C 0, |z.im - ζ.im| ≤ H := by
    intro z hz
    apply (abs_sub _ _).trans
    have hi := (abs_im_le_norm z).trans (hnorm z hz)
    dsimp [H]
    linarith [le_max_left (B + |ζ.im|) (η 0)]
  have hbounds := filledRayInset_coordinate_bounds (ζ := ζ) (s := s 0) (η := η 0)
    hCre hCim (min_le_right _ _) (le_max_right _ _)
  let J := filledRayInset (C 0) ζ (s 0) (η 0) ∩ {z : ℂ | z.re ≤ A}
  have hJ : IsCompact J := FunctionTheory.isCompact_left_truncation_of_strip_bounds
    (ComplexApproximation.isClosed_fill ((hC 0).isClosed.union (isClosed_closedHalfStrip ζ (s 0) (η 0))))
    (fun z hz => (hbounds z hz).1)
    (M := H + |ζ.im|) (fun z hz => by
      have hi := abs_le.mp (hbounds z hz).2
      apply abs_le.mpr
      constructor <;> linarith [hi.1, hi.2, neg_abs_le ζ.im, le_abs_self ζ.im])
  have hholes : ∀ n, ComplexApproximation.fill (E n) \ E n ⊆ J := by
    intro n z hz
    refine ⟨ComplexApproximation.fill_mono (hEanti (Nat.zero_le n)) hz.1, ?_⟩
    by_contra hzA
    have hzA' : A < z.re := lt_of_not_ge hzA
    have hright : ∀ w ∈ C n, w.re ≤ B :=
      fun w hw => (re_le_norm w).trans (hnorm w (hCanti (Nat.zero_le n) hw))
    have hzs : ζ.re - s n ≤ z.re := by
      have : ζ.re ≤ A := le_max_right _ _
      linarith [hs n]
    have hi := (filledRayInset_tail_iff hright
      ((le_max_left B ζ.re).trans_lt hzA') hzs).mp hz.1
    exact hz.2 (Or.inr ⟨hzs, hi⟩)
  have heq := ComplexApproximation.iInter_fill_eq_of_uniformly_bounded_holes
    (fun n => (hC n).isClosed.union (isClosed_closedHalfStrip ζ (s n) (η n)))
    hEanti (hinter.symm ▸ hfull) hJ.isBounded hholes
  exact heq.trans hinter

end EremenkosConjecture
