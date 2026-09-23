import ComplexApproximation.HalfStripProjection
import ComplexApproximation.Topology.HorizontalEscape

/-! # A U-shaped band together with a nested half-strip

These explicit closed sets have no bounded complementary components and
satisfy the bounded-holes condition for Arakelian approximation.
-/

open Set Metric Bornology Complex

namespace ComplexApproximation

def openRightHalfStrip (a b : ℝ) : Set ℂ := {z | a < z.re ∧ |z.im| < b}

def halfStripBand (a₀ a₁ b₀ b₁ : ℝ) : Set ℂ :=
  closedRightHalfStrip a₀ b₀ \ openRightHalfStrip a₁ b₁

def bandAndHalfStrip (a₀ a₁ a₂ b₀ b₁ b₂ : ℝ) : Set ℂ :=
  halfStripBand a₀ a₁ b₀ b₁ ∪ closedRightHalfStrip a₂ b₂

theorem isClosed_closedRightHalfStrip (a b : ℝ) : IsClosed (closedRightHalfStrip a b) :=
  (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_le Complex.continuous_im.abs continuous_const)

theorem isOpen_openRightHalfStrip (a b : ℝ) : IsOpen (openRightHalfStrip a b) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_im.abs continuous_const)

theorem isClosed_bandAndHalfStrip (a₀ a₁ a₂ b₀ b₁ b₂ : ℝ) :
    IsClosed (bandAndHalfStrip a₀ a₁ a₂ b₀ b₁ b₂) :=
  ((isClosed_closedRightHalfStrip a₀ b₀).sdiff (isOpen_openRightHalfStrip a₁ b₁)).union
    (isClosed_closedRightHalfStrip a₂ b₂)

private theorem right_corridor_ray {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ} {z : ℂ}
    (hre : a₁ < z.re) (hlo : b₂ < |z.im|) (hhi : |z.im| < b₁)
    {t : ℝ} (ht : 0 ≤ t) : z + (t : ℂ) ∉ bandAndHalfStrip a₀ a₁ a₂ b₀ b₁ b₂ := by
  rintro (⟨_, hn⟩ | ⟨_, hb⟩)
  · apply hn
    constructor
    · change a₁ < z.re + t
      linarith
    · simpa only [add_im, ofReal_im, add_zero] using hhi
  · have : |z.im| ≤ b₂ := by simpa only [add_im, ofReal_im, add_zero] using hb
    linarith

theorem noBoundedComplementComponents_bandAndHalfStrip {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ}
    (ha₀ : a₀ < a₁) (ha₁ : a₁ < a₂) (hb₂ : 0 ≤ b₂)
    (hb₁ : b₂ < b₁) (hb₀ : b₁ < b₀) :
    NoBoundedComplementComponents (bandAndHalfStrip a₀ a₁ a₂ b₀ b₁ b₂) := by
  intro z hz
  by_cases hleft : z.re < a₀
  · apply not_isBounded_component_of_left_ray
    intro t ht
    rintro (⟨⟨hr, _⟩, _⟩ | ⟨hr, _⟩) <;>
      change _ ≤ z.re - t at hr <;> linarith
  by_cases hout : b₀ < |z.im|
  · apply not_isBounded_component_of_right_ray
    intro t _
    rintro (⟨⟨_, hi⟩, _⟩ | ⟨_, hi⟩) <;>
      simp only [add_im, ofReal_im, add_zero] at hi <;> linarith
  have houter : z ∈ closedRightHalfStrip a₀ b₀ := ⟨le_of_not_gt hleft, le_of_not_gt hout⟩
  have hinner : z ∈ openRightHalfStrip a₁ b₁ := by
    by_contra h
    exact hz (Or.inl ⟨houter, h⟩)
  by_cases hheight : b₂ < |z.im|
  · exact not_isBounded_component_of_right_ray (fun _ ht => right_corridor_ray hinner.1 hheight hinner.2 ht)
  have hrea₂ : z.re < a₂ := lt_of_not_ge (fun h => hz (Or.inr ⟨h, le_of_not_gt hheight⟩))
  let Q : Set ℂ := {w | a₁ < w.re ∧ w.re < a₂ ∧ |w.im| < b₁}
  have hQ : Convex ℝ Q := by
    have heq : Q = {w : ℂ | a₁ < w.re} ∩ ({w : ℂ | w.re < a₂} ∩
        ({w : ℂ | -b₁ < w.im} ∩ {w : ℂ | w.im < b₁})) := by
      ext w
      simp [Q, abs_lt]
    rw [heq]
    exact (convex_halfSpace_re_gt _).inter ((convex_halfSpace_re_lt _).inter
      ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _)))
  have hQE : Q ⊆ (bandAndHalfStrip a₀ a₁ a₂ b₀ b₁ b₂)ᶜ := by
    rintro w ⟨hw₁, hw₂, hwi⟩ (⟨_, hn⟩ | ⟨hr, _⟩)
    · exact hn ⟨hw₁, hwi⟩
    · linarith
  let w : ℂ := ⟨z.re, (b₁ + b₂) / 2⟩
  have hwim : |w.im| = (b₁ + b₂) / 2 := abs_of_nonneg (by dsimp [w]; linarith)
  have hwQ : w ∈ Q := ⟨hinner.1, hrea₂, by rw [hwim]; linarith⟩
  have hzQ : z ∈ Q := ⟨hinner.1, hrea₂, hinner.2⟩
  have hwC := hQ.isPreconnected.subset_connectedComponentIn hzQ hQE hwQ
  have hwu : ¬ IsBounded (connectedComponentIn (bandAndHalfStrip a₀ a₁ a₂ b₀ b₁ b₂)ᶜ w) :=
    not_isBounded_component_of_right_ray (fun _ ht => right_corridor_ray hwQ.1
      (by rw [hwim]; linarith) hwQ.2.2 ht)
  rwa [connectedComponentIn_eq hwC]

theorem isArakelian_bandAndHalfStrip {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ}
    (ha₀ : a₀ < a₁) (ha₁ : a₁ < a₂) (hb₂ : 0 ≤ b₂)
    (hb₁ : b₂ < b₁) (hb₀ : b₁ < b₀) :
    IsArakelian (bandAndHalfStrip a₀ a₁ a₂ b₀ b₁ b₂) := by
  let F := bandAndHalfStrip a₀ a₁ a₂ b₀ b₁ b₂
  refine ⟨isClosed_bandAndHalfStrip ..,
    noBoundedComplementComponents_bandAndHalfStrip ha₀ ha₁ hb₂ hb₁ hb₀, ?_⟩
  intro R
  let S := max R 0 + |a₀| + |a₂| + |b₀| + 1
  apply (isBounded_closedBall (x := (0 : ℂ)) (r := S)).subset
  rintro z ⟨hzfill, hzF⟩
  apply mem_closedBall_zero_iff.mpr
  by_contra hn
  have hzS : S < ‖z‖ := lt_of_not_ge hn
  have hR : R < ‖z‖ := by
    dsimp [S] at hzS
    linarith [le_max_left R 0, abs_nonneg a₀, abs_nonneg a₂, abs_nonneg b₀]
  have hnorm (t : ℝ) (ht : 0 ≤ t) (hpos : 0 ≤ z.re) : z + (t : ℂ) ∉ closedBall 0 R :=
    fun h => (not_lt_of_ge (mem_closedBall_zero_iff.mp h))
      (hR.trans_le (norm_le_norm_add_real hpos ht))
  have hnorm' (t : ℝ) (ht : 0 ≤ t) (hneg : z.re ≤ 0) : z - (t : ℂ) ∉ closedBall 0 R :=
    fun h => (not_lt_of_ge (mem_closedBall_zero_iff.mp h))
      (hR.trans_le (norm_le_norm_sub_real hneg ht))
  have hunb : ¬ IsBounded (connectedComponentIn (F ∪ closedBall 0 R)ᶜ z) := by
    by_cases hout : b₀ < |z.im|
    · apply not_isBounded_component_of_horizontal_escape
      intro w hwim hnormw
      rintro ((⟨⟨_, hi⟩, _⟩ | ⟨_, hi⟩) | hwR)
      · rw [hwim] at hi
        linarith
      · rw [hwim] at hi
        linarith
      · exact (not_lt_of_ge (mem_closedBall_zero_iff.mp hwR)) (hR.trans_le hnormw)
    have hzi : |z.im| ≤ b₀ := le_of_not_gt hout
    have hzn := Complex.norm_le_abs_re_add_abs_im z
    by_cases hpos : 0 ≤ z.re
    · rw [abs_of_nonneg hpos] at hzn
      have hza₀ : a₀ ≤ z.re := by
        dsimp [S] at hzS
        linarith [le_abs_self a₀, le_abs_self b₀, le_max_right R 0, abs_nonneg a₂]
      have hza₂ : a₂ ≤ z.re := by
        dsimp [S] at hzS
        linarith [le_abs_self a₂, le_abs_self b₀, le_max_right R 0, abs_nonneg a₀]
      have hinner : z ∈ openRightHalfStrip a₁ b₁ := by
        by_contra h
        exact hzF (Or.inl ⟨⟨hza₀, hzi⟩, h⟩)
      have hheight : b₂ < |z.im| := lt_of_not_ge (fun h => hzF (Or.inr ⟨hza₂, h⟩))
      apply not_isBounded_component_of_right_ray
      intro t ht
      rintro (hw | hw)
      · exact right_corridor_ray hinner.1 hheight hinner.2 ht hw
      · exact hnorm t ht hpos hw
    · have hneg := le_of_not_ge hpos
      rw [abs_of_nonpos hneg] at hzn
      have hza₀ : z.re < a₀ := by
        dsimp [S] at hzS
        linarith [neg_abs_le a₀, le_abs_self b₀, le_max_right R 0, abs_nonneg a₂]
      apply not_isBounded_component_of_left_ray
      intro t ht
      rintro ((⟨⟨hr, _⟩, _⟩ | ⟨hr, _⟩) | hw)
      · change a₀ ≤ z.re - t at hr
        linarith
      · change a₂ ≤ z.re - t at hr
        linarith
      · exact hnorm' t ht hneg hw
  exact hunb hzfill

end ComplexApproximation
