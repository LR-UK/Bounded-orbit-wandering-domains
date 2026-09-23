import ComplexApproximation.Topology.Filling

/-!
# Arakelian's bounded-holes condition and an exhaustion

We use the planar formulation of the geometric condition: there are no bounded
complementary components, and the holes created by adjoining any disk have
bounded union. This is the condition used in the Rosay–Rudin proof.
-/

open Set Metric Bornology

namespace ComplexApproximation

/-- The closed-set, no-holes, bounded-exhaustion-holes formulation of Arakelian's
geometric hypothesis. -/
structure IsArakelian (E : Set ℂ) : Prop where
  isClosed : IsClosed E
  noBoundedComplementComponents : NoBoundedComplementComponents E
  boundedHoles : ∀ R : ℝ, IsBounded (fill (E ∪ closedBall 0 R) \ E)

def arakelianExhaustion (E : Set ℂ) (n : ℕ) : Set ℂ :=
  if n = 0 then E else fill (E ∪ closedBall 0 (n : ℝ))

@[simp] theorem arakelianExhaustion_zero (E : Set ℂ) : arakelianExhaustion E 0 = E := by
  simp [arakelianExhaustion]

theorem arakelianExhaustion_succ (E : Set ℂ) (n : ℕ) :
    arakelianExhaustion E (n + 1) = fill (E ∪ closedBall 0 ((n + 1 : ℕ) : ℝ)) := by
  simp [arakelianExhaustion]

theorem subset_arakelianExhaustion (E : Set ℂ) (n : ℕ) : E ⊆ arakelianExhaustion E n := by
  by_cases hn : n = 0
  · simp [arakelianExhaustion, hn]
  · simpa only [arakelianExhaustion, if_neg hn] using
      (subset_union_left.trans (subset_fill (E ∪ closedBall 0 (n : ℝ))))

theorem arakelianExhaustion_mono (E : Set ℂ) : Monotone (arakelianExhaustion E) := by
  intro m n hmn
  by_cases hm : m = 0
  · simpa [hm] using subset_arakelianExhaustion E n
  · have hn : n ≠ 0 := by omega
    simp only [arakelianExhaustion, if_neg hm, if_neg hn]
    apply fill_mono (union_subset_union_right E _)
    exact closedBall_subset_closedBall (by exact_mod_cast hmn)

theorem isClosed_arakelianExhaustion {E : Set ℂ} (hE : IsClosed E) (n : ℕ) :
    IsClosed (arakelianExhaustion E n) := by
  by_cases hn : n = 0
  · simpa [arakelianExhaustion, hn] using hE
  · simpa only [arakelianExhaustion, if_neg hn] using
      isClosed_fill (hE.union isClosed_closedBall)

theorem noBoundedComplementComponents_arakelianExhaustion {E : Set ℂ}
    (hE : NoBoundedComplementComponents E) (n : ℕ) :
    NoBoundedComplementComponents (arakelianExhaustion E n) := by
  by_cases hn : n = 0
  · simpa [arakelianExhaustion, hn] using hE
  · simpa only [arakelianExhaustion, if_neg hn] using
      noBoundedComplementComponents_fill (E ∪ closedBall 0 (n : ℝ))

theorem IsArakelian.isBounded_exhaustion_diff {E : Set ℂ} (hE : IsArakelian E) (n : ℕ) :
    IsBounded (arakelianExhaustion E n \ E) := by
  by_cases hn : n = 0
  · simpa [hn] using (isBounded_empty : IsBounded (∅ : Set ℂ))
  · simpa only [arakelianExhaustion, if_neg hn] using hE.boundedHoles (n : ℝ)

theorem IsArakelian.isBounded_exhaustion_succ_diff {E : Set ℂ} (hE : IsArakelian E) (n : ℕ) :
    IsBounded (arakelianExhaustion E (n + 1) \ arakelianExhaustion E n) :=
  (hE.isBounded_exhaustion_diff (n + 1)).subset
    (diff_subset_diff_right (subset_arakelianExhaustion E n))

theorem closedBall_subset_arakelianExhaustion (E : Set ℂ) {n : ℕ} (hn : n ≠ 0) :
    closedBall 0 (n : ℝ) ⊆ arakelianExhaustion E n := by
  simp only [arakelianExhaustion, if_neg hn]
  exact subset_union_right.trans (subset_fill _)

end ComplexApproximation
