import EremenkosConjecture.ScaffoldingStability
import ComplexApproximation.Topology.StripArakelian

/-! # Expanding horizontal backgrounds used in Section 7 -/

open Set Metric Complex ComplexApproximation

namespace EremenkosConjecture.Scaffolding

def centralBand (j : ℕ) : Set ℂ := {z | 4 * |z.im| ≤ height j + 3}
def background (j : ℕ) : Set ℂ := closedSourceStrips ∪ centralBand j
def backgroundLevels (j : ℕ) : Set ℝ := horizontalLevels ∪ {y | 4 * |y| ≤ height j + 3}

theorem height_monotone : Monotone height := monotone_nat_of_le_succ fun j => by
  rw [height_succ]
  linarith [five_le_height j]

theorem background_eq_horizontalLift (j : ℕ) : background j = horizontalLift (backgroundLevels j) := by
  rw [background, closedSourceStrips_eq_horizontalLift]
  rfl

theorem isClosed_backgroundLevels (j : ℕ) : IsClosed (backgroundLevels j) :=
  isClosed_horizontalLevels.union (isClosed_le (continuous_const.mul continuous_abs) continuous_const)

theorem isArakelian_background (j : ℕ) : IsArakelian (background j) := by
  rw [background_eq_horizontalLift]
  exact isArakelian_horizontalLift (isClosed_backgroundLevels j)

theorem background_monotone : Monotone background := by
  intro j k hjk z hz
  rcases hz with hz | hz
  · exact Or.inl hz
  · apply Or.inr
    change 4 * |z.im| ≤ height k + 3
    change 4 * |z.im| ≤ height j + 3 at hz
    linarith [height_monotone hjk]

theorem sourceStrips_subset_background (j : ℕ) : sourceStrips ⊆ background j := by
  intro z hz
  obtain ⟨k, hk⟩ := mem_iUnion.mp hz
  exact Or.inl (mem_iUnion.mpr ⟨k, sourceStrip_subset_closed k hk⟩)

theorem closedSourceStrips_subset_background (j : ℕ) : closedSourceStrips ⊆ background j :=
  subset_union_left

theorem trappingDisk_subset_background (j : ℕ) : trappingDisk ⊆ background j := by
  intro z hz
  have hnorm := mem_closedBall_zero_iff.mp hz
  have him := (Complex.abs_im_le_norm z).trans hnorm
  apply Or.inr
  change 4 * |z.im| ≤ height j + 3
  linarith [five_le_height j]

theorem targetStrip_eq_openHorizontalStrip (j : ℕ) :
    targetStrip j = openHorizontalStrip ((height j + 7) / 4) ((height j + 11) / 4) := by
  ext z
  change (height j + 7 < 4 * z.im ∧ 4 * z.im < height j + 11) ↔
    ((height j + 7) / 4 < z.im ∧ z.im < (height j + 11) / 4)
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem disjoint_background_targetStrip (j : ℕ) : Disjoint (background j) (targetStrip j) := by
  apply disjoint_left.mpr
  intro z hz ht
  rcases hz with hz | hz
  · obtain ⟨k, hk⟩ := mem_iUnion.mp hz
    by_cases hkj : k ≤ j
    · have hh := height_monotone hkj
      linarith [hk.2, ht.1]
    · have hh := height_monotone (show j + 1 ≤ k by omega)
      rw [height_succ] at hh
      linarith [hk.1, ht.2, five_le_height j]
  · change 4 * |z.im| ≤ height j + 3 at hz
    linarith [ht.1, le_abs_self z.im]

theorem ball_inset_subset_background (j k : ℕ) {z : ℂ} (hz : z ∈ insetSourceStrip k) :
    ball z (1 / 10) ⊆ background j :=
  (ball_inset_subset_source hz).trans
    ((subset_iUnion _ k).trans (sourceStrips_subset_background j))

theorem ball_target_subset_next_background {j : ℕ} {z : ℂ} (hz : z ∈ targetStrip j) :
    ball z (1 / 4) ⊆ background (j + 1) := by
  intro w hw
  have hd : ‖w - z‖ < (1 / 4 : ℝ) := by simpa only [mem_ball, dist_eq_norm] using hw
  have hi := (Complex.abs_im_le_norm (w - z)).trans_lt hd
  simp only [Complex.sub_im] at hi
  have hzi : 0 < z.im := by linarith [hz.1, five_le_height j]
  have him := abs_add_le (w.im - z.im) z.im
  rw [sub_add_cancel, abs_of_pos hzi] at him
  apply Or.inr
  change 4 * |w.im| ≤ height (j + 1) + 3
  rw [height_succ]
  linarith [hz.2, five_le_height j]

theorem closedBall_subset_background (j : ℕ) : closedBall (0 : ℂ) ((j : ℝ) / 4) ⊆ background j := by
  intro z hz
  apply Or.inr
  have hi := (Complex.abs_im_le_norm z).trans (mem_closedBall_zero_iff.mp hz)
  change 4 * |z.im| ≤ height j + 3
  linarith [nat_le_height j]

theorem background_exhausts_closedBalls (R : ℝ) :
    ∃ N : ℕ, ∀ j ≥ N, closedBall (0 : ℂ) R ⊆ background j := by
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * R)
  refine ⟨N, fun j hj => ?_⟩
  apply (closedBall_subset_closedBall ?_).trans (closedBall_subset_background j)
  have hj' : (N : ℝ) ≤ j := by exact_mod_cast hj
  linarith

end EremenkosConjecture.Scaffolding
