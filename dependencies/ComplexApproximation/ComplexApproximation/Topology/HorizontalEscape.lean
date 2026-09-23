import ComplexApproximation.Topology.HorizontalSets

/-! # Outward horizontal rays as witnesses of unbounded components -/

open Set Metric Bornology Complex

namespace ComplexApproximation

/-- A ray in any nonzero complex direction witnesses an unbounded component. -/
theorem not_isBounded_component_of_affine_ray {E : Set ℂ} {z v : ℂ}
    (hv : v ≠ 0) (hray : ∀ t : ℝ, 0 ≤ t → z + (t : ℂ) * v ∈ E) :
    ¬ IsBounded (connectedComponentIn E z) := by
  let γ : ℝ → ℂ := fun t => z + (t : ℂ) * v
  have hγ : Continuous γ := by fun_prop
  have hz : z ∈ γ '' Ici 0 := ⟨0, by simp, by simp [γ]⟩
  have hsub : γ '' Ici 0 ⊆ E := by rintro w ⟨t, ht, rfl⟩; exact hray t ht
  have hc := (isConnected_Ici.image γ hγ.continuousOn).isPreconnected.subset_connectedComponentIn hz hsub
  intro hb
  obtain ⟨M, hM, hbound⟩ := hb.exists_pos_norm_le
  let t := (M + ‖z‖ + 1) / ‖v‖
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hn := norm_sub_le (γ t) z
  have hγbound := hbound _ (hc ⟨t, ht, rfl⟩)
  have hn' : t * ‖v‖ ≤ M + ‖z‖ := by
    simpa only [γ, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht] using
        hn.trans (show ‖γ t‖ + ‖z‖ ≤ M + ‖z‖ by linarith)
  have heq : t * ‖v‖ = M + ‖z‖ + 1 := div_mul_cancel₀ _ hvp.ne'
  linarith

theorem exists_unbounded_horizontal_set (z : ℂ) : ∃ C : Set ℂ,
    IsConnected C ∧ z ∈ C ∧ ¬ IsBounded C ∧
    ∀ w ∈ C, w.im = z.im ∧ ‖z‖ ≤ ‖w‖ := by
  classical
  let γ : ℝ → ℂ := if 0 ≤ z.re then (fun t => z + (t : ℂ)) else (fun t => z - (t : ℂ))
  have hγ : Continuous γ := by dsimp [γ]; split_ifs <;> fun_prop
  have hγ0 : γ 0 = z := by dsimp [γ]; split_ifs <;> simp
  refine ⟨γ '' Ici 0, isConnected_Ici.image γ hγ.continuousOn,
    ⟨0, by simp, hγ0⟩, ?_, ?_⟩
  · intro hb
    obtain ⟨M, hM, hbound⟩ := hb.exists_pos_norm_le
    have hm : γ (M + 1) ∈ γ '' Ici 0 := ⟨M + 1, by change 0 ≤ M + 1; linarith, rfl⟩
    have hre := abs_le.mp ((abs_re_le_norm (γ (M + 1))).trans (hbound _ hm))
    dsimp [γ] at hre
    split_ifs at hre with h
    · simp only [add_re, ofReal_re] at hre
      linarith [hre.2]
    · simp only [sub_re, ofReal_re] at hre
      linarith [hre.1]
  · rintro w ⟨t, ht, rfl⟩
    constructor
    · dsimp [γ]; split_ifs <;> simp
    · dsimp [γ]
      split_ifs with h
      · exact norm_le_norm_add_real h ht
      · exact norm_le_norm_sub_real (le_of_not_ge h) ht

theorem not_isBounded_component_of_horizontal_escape {E : Set ℂ} {z : ℂ}
    (hescape : ∀ w : ℂ, w.im = z.im → ‖z‖ ≤ ‖w‖ → w ∈ E) :
    ¬ IsBounded (connectedComponentIn E z) := by
  obtain ⟨C, hC, hzC, hunb, hprops⟩ := exists_unbounded_horizontal_set z
  have hCE : C ⊆ E := fun w hw => hescape w (hprops w hw).1 (hprops w hw).2
  exact fun hb => hunb (hb.subset (hC.isPreconnected.subset_connectedComponentIn hzC hCE))

theorem not_isBounded_component_of_right_ray {E : Set ℂ} {z : ℂ}
    (hray : ∀ t : ℝ, 0 ≤ t → z + (t : ℂ) ∈ E) :
    ¬ IsBounded (connectedComponentIn E z) := by
  let γ : ℝ → ℂ := fun t => z + (t : ℂ)
  have hγ : Continuous γ := by fun_prop
  have hz : z ∈ γ '' Ici 0 := ⟨0, by simp, by simp [γ]⟩
  have hsub : γ '' Ici 0 ⊆ E := by rintro w ⟨t, ht, rfl⟩; exact hray t ht
  have hc := (isConnected_Ici.image γ hγ.continuousOn).isPreconnected.subset_connectedComponentIn hz hsub
  intro hb
  obtain ⟨M, hM, hbound⟩ := hb.exists_pos_norm_le
  let t := M + |z.re| + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hn := (Complex.re_le_norm (γ t)).trans (hbound _ (hc ⟨t, ht, rfl⟩))
  change z.re + t ≤ M at hn
  dsimp [t] at hn
  linarith [neg_abs_le z.re]

theorem not_isBounded_component_of_left_ray {E : Set ℂ} {z : ℂ}
    (hray : ∀ t : ℝ, 0 ≤ t → z - (t : ℂ) ∈ E) :
    ¬ IsBounded (connectedComponentIn E z) := by
  let γ : ℝ → ℂ := fun t => z - (t : ℂ)
  have hγ : Continuous γ := by fun_prop
  have hz : z ∈ γ '' Ici 0 := ⟨0, by simp, by simp [γ]⟩
  have hsub : γ '' Ici 0 ⊆ E := by rintro w ⟨t, ht, rfl⟩; exact hray t ht
  have hc := (isConnected_Ici.image γ hγ.continuousOn).isPreconnected.subset_connectedComponentIn hz hsub
  intro hb
  obtain ⟨M, hM, hbound⟩ := hb.exists_pos_norm_le
  let t := M + |z.re| + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hn := (abs_le.mp ((Complex.abs_re_le_norm (γ t)).trans (hbound _ (hc ⟨t, ht, rfl⟩)))).1
  change -M ≤ z.re - t at hn
  dsimp [t] at hn
  linarith [le_abs_self z.re]

end ComplexApproximation
