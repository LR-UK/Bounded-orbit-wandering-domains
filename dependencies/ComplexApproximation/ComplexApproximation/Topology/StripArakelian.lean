import ComplexApproximation.Topology.StripLocalisation

/-! # Adding an Arakelian set inside one horizontal gap -/

open Set Metric Bornology Complex
open scoped Topology

namespace ComplexApproximation

theorem strip_boundary_collars {F : Set ℂ} {l u a b R S : ℝ}
    (hla : l < a) (hbu : b < u)
    (hF : F ⊆ {z | a ≤ z.im ∧ z.im ≤ b})
    (hlarge : ∀ w ∈ frontier (openHorizontalStrip l u), w ∉ closedBall 0 S → R < |w.re|) :
    ∀ w ∈ frontier (openHorizontalStrip l u), w ∉ closedBall 0 S →
      ∃ O : Set ℂ, IsOpen O ∧ w ∈ O ∧ ∀ v ∈ O ∩ openHorizontalStrip l u,
        ¬ IsBounded (connectedComponentIn (openHorizontalStrip l u \ (F ∪ closedBall 0 R)) v) := by
  have hescape (v : ℂ) (hv : v ∈ openHorizontalStrip l u)
      (hvr : R < |v.re|) (hvi : v.im < a ∨ b < v.im) :
      ¬ IsBounded (connectedComponentIn (openHorizontalStrip l u \ (F ∪ closedBall 0 R)) v) := by
    apply not_isBounded_component_of_horizontal_escape
    intro w hwim hnorm
    refine ⟨by simpa only [openHorizontalStrip, mem_ofPred_eq, hwim] using hv, ?_⟩
    rintro (hwF | hwR)
    · obtain ⟨ha, hb⟩ := hF hwF
      rw [hwim] at ha hb
      rcases hvi with h | h <;> linarith
    · exact (not_lt_of_ge (mem_closedBall_zero_iff.mp hwR))
        (hvr.trans_le ((Complex.abs_re_le_norm v).trans hnorm))
  intro w hw hwS
  have hwr := hlarge w hw hwS
  rcases frontier_openHorizontalStrip hw with hwl | hwu
  · refine ⟨{v : ℂ | v.im < a ∧ R < |v.re|},
      (isOpen_lt Complex.continuous_im continuous_const).inter
        (isOpen_lt continuous_const Complex.continuous_re.abs),
      ⟨by simpa only [hwl] using hla, hwr⟩, ?_⟩
    intro v hv
    exact hescape v hv.2 hv.1.2 (Or.inl hv.1.1)
  · refine ⟨{v : ℂ | b < v.im ∧ R < |v.re|},
      (isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt continuous_const Complex.continuous_re.abs),
      ⟨by simpa only [hwu] using hbu, hwr⟩, ?_⟩
    intro v hv
    exact hescape v hv.2 hv.1.2 (Or.inr hv.1.1)

theorem unbounded_component_in_strip {F : Set ℂ} (hFclosed : IsClosed F)
    {l u a b R S : ℝ} (hla : l < a) (hbu : b < u)
    (hF : F ⊆ {z | a ≤ z.im ∧ z.im ≤ b}) (hRS : R ≤ S)
    (hlarge : ∀ w ∈ frontier (openHorizontalStrip l u), w ∉ closedBall 0 S → R < |w.re|)
    {z : ℂ} (hzU : z ∈ openHorizontalStrip l u) (hzF : z ∉ F ∪ closedBall 0 S)
    (hunb : ¬ IsBounded (connectedComponentIn (F ∪ closedBall 0 S)ᶜ z)) :
    ¬ IsBounded (connectedComponentIn (openHorizontalStrip l u \ (F ∪ closedBall 0 R)) z) :=
  unbounded_component_restrict_of_boundary_collars hFclosed (isOpen_openHorizontalStrip l u)
    hRS (strip_boundary_collars hla hbu hF hlarge) hzU hzF hunb

theorem unbounded_component_outside_strip {A : Set ℝ} {F : Set ℂ} {l u R : ℝ}
    (hF : F ⊆ openHorizontalStrip l u) {z : ℂ}
    (hz : z ∉ (horizontalLift A ∪ F) ∪ closedBall 0 R)
    (hzU : z ∉ openHorizontalStrip l u) :
    ¬ IsBounded (connectedComponentIn ((horizontalLift A ∪ F) ∪ closedBall 0 R)ᶜ z) := by
  apply not_isBounded_component_of_horizontal_escape
  intro w hwim hnorm
  rintro ((hwA | hwF) | hwR)
  · apply hz
    exact Or.inl (Or.inl (by simpa only [horizontalLift, mem_preimage, hwim] using hwA))
  · apply hzU
    simpa only [openHorizontalStrip, mem_ofPred_eq, hwim] using hF hwF
  · exact hz (Or.inr (mem_closedBall_zero_iff.mpr (hnorm.trans (mem_closedBall_zero_iff.mp hwR))))

/-- An Arakelian set lying with a vertical margin inside one gap can be
adjoined to any closed horizontal background that avoids that gap. -/
theorem IsArakelian.union_horizontal_background {F : Set ℂ} (hF : IsArakelian F)
    {A : Set ℝ} (hA : IsClosed A) {l u a b : ℝ} (hla : l < a) (hbu : b < u)
    (hband : F ⊆ {z | a ≤ z.im ∧ z.im ≤ b})
    (hgap : Disjoint (horizontalLift A) (openHorizontalStrip l u)) :
    IsArakelian (horizontalLift A ∪ F) := by
  have hFU : F ⊆ openHorizontalStrip l u := fun z hz =>
    ⟨hla.trans_le (hband hz).1, (hband hz).2.trans_lt hbu⟩
  have hsub (R : ℝ) : openHorizontalStrip l u \ (F ∪ closedBall 0 R) ⊆
      ((horizontalLift A ∪ F) ∪ closedBall 0 R)ᶜ := by
    rintro z ⟨hzU, hzF⟩ ((hzA | hzF') | hzR)
    · exact Set.disjoint_left.mp hgap hzA hzU
    · exact hzF (Or.inl hzF')
    · exact hzF (Or.inr hzR)
  refine ⟨(hA.preimage Complex.continuous_im).union hF.isClosed, ?_, ?_⟩
  · intro z hz
    have hball : closedBall (0 : ℂ) (-1) = ∅ := closedBall_eq_empty.mpr (by norm_num)
    have hz' : z ∉ (horizontalLift A ∪ F) ∪ closedBall 0 (-1) := by simpa [hball] using hz
    have hunb : ¬ IsBounded (connectedComponentIn ((horizontalLift A ∪ F) ∪ closedBall 0 (-1))ᶜ z) := by
      by_cases hzU : z ∈ openHorizontalStrip l u
      · have hzF : z ∉ F ∪ closedBall 0 (-1) := fun h => hz' (h.imp (fun h => Or.inr h) id)
        have hwhole : ¬ IsBounded (connectedComponentIn (F ∪ closedBall 0 (-1))ᶜ z) := by
          simpa only [hball, union_empty] using hF.noBoundedComplementComponents z (fun h => hz (Or.inr h))
        have hlocal := unbounded_component_in_strip hF.isClosed hla hbu hband le_rfl
          (fun w _ _ => by linarith [abs_nonneg w.re]) hzU hzF hwhole
        exact fun hb => hlocal (hb.subset (connectedComponentIn_mono z (hsub (-1))))
      · exact unbounded_component_outside_strip hFU hz' hzU
    simpa only [hball, union_empty] using hunb
  · intro R
    let S := max R 0 + |l| + |u| + 1
    have hRS : R ≤ S := by dsimp [S]; linarith [le_max_left R 0, abs_nonneg l, abs_nonneg u]
    have hlarge : ∀ w ∈ frontier (openHorizontalStrip l u), w ∉ closedBall 0 S → R < |w.re| := by
      intro w hw hwS
      have hn : S < ‖w‖ := lt_of_not_ge (fun h => hwS (mem_closedBall_zero_iff.mpr h))
      have hnorm := Complex.norm_le_abs_re_add_abs_im w
      rcases frontier_openHorizontalStrip hw with hw | hw
      · rw [hw] at hnorm
        dsimp [S] at hn
        linarith [le_max_left R 0, abs_nonneg u]
      · rw [hw] at hnorm
        dsimp [S] at hn
        linarith [le_max_left R 0, abs_nonneg l]
    obtain ⟨M, hM, hbound⟩ := (hF.boundedHoles S).exists_pos_norm_le
    apply (isBounded_closedBall (x := (0 : ℂ)) (r := max M S)).subset
    rintro z ⟨hzfill, hzE⟩
    apply mem_closedBall_zero_iff.mpr
    by_contra hn
    have hzn : max M S < ‖z‖ := lt_of_not_ge hn
    have hzS : S < ‖z‖ := (le_max_right M S).trans_lt hzn
    have hz' : z ∉ (horizontalLift A ∪ F) ∪ closedBall 0 R := by
      rintro (hz | hz)
      · exact hzE hz
      · exact (not_lt_of_ge (mem_closedBall_zero_iff.mp hz)) (hRS.trans_lt hzS)
    have hunb : ¬ IsBounded (connectedComponentIn ((horizontalLift A ∪ F) ∪ closedBall 0 R)ᶜ z) := by
      by_cases hzU : z ∈ openHorizontalStrip l u
      · have hzF : z ∉ F ∪ closedBall 0 S := by
          rintro (hz | hz)
          · exact hzE (Or.inr hz)
          · exact (not_lt_of_ge (mem_closedBall_zero_iff.mp hz)) hzS
        have hwhole : ¬ IsBounded (connectedComponentIn (F ∪ closedBall 0 S)ᶜ z) := by
          intro hb
          have hle := hbound z ⟨hb, fun h => hzE (Or.inr h)⟩
          exact (not_lt_of_ge hle) ((le_max_left M S).trans_lt hzn)
        have hlocal := unbounded_component_in_strip hF.isClosed hla hbu hband hRS hlarge hzU hzF hwhole
        exact fun hb => hlocal (hb.subset (connectedComponentIn_mono z (hsub R)))
      · exact unbounded_component_outside_strip hFU hz' hzU
    exact hunb hzfill

end ComplexApproximation
