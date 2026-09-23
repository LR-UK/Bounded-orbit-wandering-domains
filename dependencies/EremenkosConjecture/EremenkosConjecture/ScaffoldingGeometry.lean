import ComplexApproximation.Topology.HorizontalSets
import Mathlib.Topology.LocallyFinite
import Mathlib.Tactic.Linarith

/-! # The horizontal strips and return times of Section 4 -/

open Set Metric Complex ComplexApproximation
open scoped Topology

namespace EremenkosConjecture.Scaffolding

def height (j : ℕ) : ℝ := 5 ^ (j + 1)

def sourceStrip (j : ℕ) : Set ℂ :=
  {z | height j - 1 < 4 * z.im ∧ 4 * z.im < height j + 3}

def closedSourceStrip (j : ℕ) : Set ℂ :=
  {z | height j - 1 ≤ 4 * z.im ∧ 4 * z.im ≤ height j + 3}

def targetStrip (j : ℕ) : Set ℂ :=
  {z | height j + 7 < 4 * z.im ∧ 4 * z.im < height j + 11}

def insetSourceStrip (j : ℕ) : Set ℂ :=
  {z | height j - 3 / 5 ≤ 4 * z.im ∧ 4 * z.im ≤ height j + 13 / 5}

def sourceStrips : Set ℂ := ⋃ j, sourceStrip j
def closedSourceStrips : Set ℂ := ⋃ j, closedSourceStrip j
def trappingDisk : Set ℂ := closedBall 0 (1 / 2)
def initialApproximationSet : Set ℂ := closedSourceStrips ∪ trappingDisk

def returnTime : ℕ → ℕ
  | 0 => 0
  | j + 1 => returnTime j + j + 2

@[simp] theorem returnTime_zero : returnTime 0 = 0 := rfl
@[simp] theorem returnTime_succ (j : ℕ) : returnTime (j + 1) = returnTime j + j + 2 := rfl

theorem two_mul_returnTime (j : ℕ) : 2 * returnTime j = j * (j + 3) := by
  induction j with
  | zero => simp
  | succ j hj => rw [returnTime_succ]; nlinarith

theorem returnTime_eq (j : ℕ) : returnTime j = j * (j + 3) / 2 := by
  have h := two_mul_returnTime j
  omega

theorem height_succ (j : ℕ) : height (j + 1) = 5 * height j := by
  simp only [height, pow_succ]
  ring

theorem five_le_height (j : ℕ) : 5 ≤ height j := by
  induction j with
  | zero => norm_num [height]
  | succ j hj => rw [height_succ]; linarith

theorem nat_le_height (j : ℕ) : (j : ℝ) ≤ height j := by
  induction j with
  | zero => norm_num [height]
  | succ j hj => rw [height_succ, Nat.cast_add, Nat.cast_one]; nlinarith [five_le_height j]

theorem isOpen_sourceStrip (j : ℕ) : IsOpen (sourceStrip j) :=
  (isOpen_lt continuous_const (continuous_const.mul Complex.continuous_im)).inter
    (isOpen_lt (continuous_const.mul Complex.continuous_im) continuous_const)

theorem isOpen_targetStrip (j : ℕ) : IsOpen (targetStrip j) :=
  (isOpen_lt continuous_const (continuous_const.mul Complex.continuous_im)).inter
    (isOpen_lt (continuous_const.mul Complex.continuous_im) continuous_const)

theorem isClosed_closedSourceStrip (j : ℕ) : IsClosed (closedSourceStrip j) :=
  (isClosed_le continuous_const (continuous_const.mul Complex.continuous_im)).inter
    (isClosed_le (continuous_const.mul Complex.continuous_im) continuous_const)

theorem sourceStrip_subset_closed (j : ℕ) : sourceStrip j ⊆ closedSourceStrip j :=
  fun _ h => ⟨h.1.le, h.2.le⟩

theorem insetSourceStrip_subset (j : ℕ) : insetSourceStrip j ⊆ sourceStrip j := by
  intro z hz
  constructor <;> dsimp [insetSourceStrip] at hz <;> linarith [hz.1, hz.2]

theorem one_le_im_of_mem_closedSourceStrips {z : ℂ} (hz : z ∈ closedSourceStrips) :
    1 ≤ z.im := by
  obtain ⟨j, hj⟩ := mem_iUnion.mp hz
  have h := five_le_height j
  have hlo := hj.1
  linarith

def horizontalLevels : Set ℝ :=
  ⋃ j : ℕ, Icc ((height j - 1) / 4) ((height j + 3) / 4)

theorem locallyFinite_levelIntervals :
    LocallyFinite (fun j : ℕ => Icc ((height j - 1) / 4) ((height j + 3) / 4)) := by
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * x + 5)
  refine ⟨Iio (x + 1), Iio_mem_nhds (by linarith), (finite_Iio N).subset ?_⟩
  rintro j ⟨y, hy, hyx⟩
  have hj := nat_le_height j
  have hcast : (j : ℝ) < N := by
    have hlo := hy.1
    change y < x + 1 at hyx
    linarith
  exact_mod_cast hcast

theorem isClosed_horizontalLevels : IsClosed horizontalLevels :=
  locallyFinite_levelIntervals.isClosed_iUnion (fun _ => isClosed_Icc)

theorem closedSourceStrips_eq_horizontalLift : closedSourceStrips = horizontalLift horizontalLevels := by
  ext z
  simp only [closedSourceStrips, horizontalLift, horizontalLevels, mem_preimage, mem_iUnion, mem_Icc]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, by constructor <;> linarith [hj.1, hj.2]⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, by constructor <;> linarith [hj.1, hj.2]⟩

theorem isArakelian_initialApproximationSet : IsArakelian initialApproximationSet := by
  rw [initialApproximationSet, closedSourceStrips_eq_horizontalLift]
  exact isArakelian_horizontalLift_union_closedBall isClosed_horizontalLevels (1 / 2)

theorem disjoint_trappingDisk_closedSourceStrips : Disjoint trappingDisk closedSourceStrips := by
  apply Set.disjoint_left.mpr
  intro z hzD hzS
  have hnorm : ‖z‖ ≤ 1 / 2 := mem_closedBall_zero_iff.mp hzD
  have him := one_le_im_of_mem_closedSourceStrips hzS
  have himnorm := le_trans (le_abs_self z.im) (abs_im_le_norm z)
  linarith

end EremenkosConjecture.Scaffolding
