import ComplexApproximation.Topology.Arakelian

/-! # Horizontal approximation sets

Any closed union of complete horizontal lines, with a centred disk adjoined,
satisfies the bounded-holes condition. An outward horizontal ray from each
complementary point stays in the complement and is unbounded.
-/

open Set Metric Bornology Complex

namespace ComplexApproximation

def horizontalLift (A : Set ℝ) : Set ℂ := Complex.im ⁻¹' A

theorem norm_le_norm_add_real {z : ℂ} {t : ℝ} (hz : 0 ≤ z.re) (ht : 0 ≤ t) :
    ‖z‖ ≤ ‖z + (t : ℂ)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, normSq_apply, add_re, ofReal_re, add_im, ofReal_im, add_zero]
  nlinarith [mul_nonneg hz ht, sq_nonneg t]

theorem norm_le_norm_sub_real {z : ℂ} {t : ℝ} (hz : z.re ≤ 0) (ht : 0 ≤ t) :
    ‖z‖ ≤ ‖z - (t : ℂ)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, normSq_apply, sub_re, ofReal_re, sub_im, ofReal_im, sub_zero]
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hz ht, sq_nonneg t]

theorem noBoundedComplementComponents_horizontalLift_union_closedBall
    (A : Set ℝ) (R : ℝ) :
    NoBoundedComplementComponents (horizontalLift A ∪ closedBall 0 R) := by
  classical
  intro z hz hb
  have hzA : z.im ∉ A := fun h => hz (Or.inl h)
  have hzR : R < ‖z‖ := by
    by_contra! H
    exact hz (Or.inr (mem_closedBall_zero_iff.mpr H))
  let γ : ℝ → ℂ := if 0 ≤ z.re then (fun t => z + (t : ℂ)) else (fun t => z - (t : ℂ))
  have hγ : Continuous γ := by dsimp [γ]; split_ifs <;> fun_prop
  have hγ0 : γ 0 = z := by dsimp [γ]; split_ifs <;> simp
  have hγim (t : ℝ) : (γ t).im = z.im := by dsimp [γ]; split_ifs <;> simp
  have hγnorm (t : ℝ) (ht : 0 ≤ t) : ‖z‖ ≤ ‖γ t‖ := by
    dsimp [γ]
    split_ifs with h
    · exact norm_le_norm_add_real h ht
    · exact norm_le_norm_sub_real (le_of_not_ge h) ht
  have hγsub : γ '' Ici 0 ⊆ (horizontalLift A ∪ closedBall 0 R)ᶜ := by
    rintro w ⟨t, ht, rfl⟩ (hw | hw)
    · exact hzA (by simpa only [horizontalLift, mem_preimage, hγim] using hw)
    · exact (not_lt_of_ge (mem_closedBall_zero_iff.mp hw)) (hzR.trans_le (hγnorm t ht))
  have hconn : IsConnected (γ '' Ici 0) := isConnected_Ici.image γ hγ.continuousOn
  have hzγ : z ∈ γ '' Ici 0 := ⟨0, by simp, hγ0⟩
  have hsub := hconn.isPreconnected.subset_connectedComponentIn hzγ hγsub
  obtain ⟨M, hM, hbound⟩ := hb.exists_pos_norm_le
  have hm : γ (M + 1) ∈ connectedComponentIn (horizontalLift A ∪ closedBall 0 R)ᶜ z :=
    hsub ⟨M + 1, by change 0 ≤ M + 1; linarith, rfl⟩
  have hre := abs_le.mp ((abs_re_le_norm (γ (M + 1))).trans (hbound _ hm))
  dsimp [γ] at hre
  split_ifs at hre with h
  · simp only [add_re, ofReal_re] at hre
    linarith [hre.2]
  · simp only [sub_re, ofReal_re] at hre
    linarith [hre.1]

theorem noBoundedComplementComponents_horizontalLift (A : Set ℝ) :
    NoBoundedComplementComponents (horizontalLift A) := by
  simpa only [closedBall_eq_empty.mpr (by norm_num : (-1 : ℝ) < 0), union_empty] using
    noBoundedComplementComponents_horizontalLift_union_closedBall A (-1)

theorem isArakelian_horizontalLift {A : Set ℝ} (hA : IsClosed A) :
    IsArakelian (horizontalLift A) := by
  refine ⟨hA.preimage Complex.continuous_im,
    noBoundedComplementComponents_horizontalLift A, ?_⟩
  intro R
  rw [fill_eq_self (noBoundedComplementComponents_horizontalLift_union_closedBall A R)]
  exact (isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset
    (fun z hz => hz.1.resolve_left hz.2)

/-- Adjoining a centred disk to a closed horizontal set still gives an
Arakelian approximation set. -/
theorem isArakelian_horizontalLift_union_closedBall {A : Set ℝ} (hA : IsClosed A)
    (r : ℝ) : IsArakelian (horizontalLift A ∪ closedBall 0 r) := by
  refine ⟨(hA.preimage Complex.continuous_im).union isClosed_closedBall,
    noBoundedComplementComponents_horizontalLift_union_closedBall A r, ?_⟩
  intro R
  have hsub : (horizontalLift A ∪ closedBall 0 r) ∪ closedBall 0 R ⊆
      horizontalLift A ∪ closedBall 0 (max r R) := by
    rintro z ((hz | hz) | hz)
    · exact Or.inl hz
    · exact Or.inr (closedBall_subset_closedBall (le_max_left r R) hz)
    · exact Or.inr (closedBall_subset_closedBall (le_max_right r R) hz)
  have hfill := fill_mono hsub
  rw [fill_eq_self (noBoundedComplementComponents_horizontalLift_union_closedBall A (max r R))]
    at hfill
  exact (isBounded_closedBall (x := (0 : ℂ)) (r := max r R)).subset
    (fun z hz => (hfill hz.1).resolve_left (fun h => hz.2 (Or.inl h)))

end ComplexApproximation
