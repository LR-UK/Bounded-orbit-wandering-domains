import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

open Set Metric

namespace FunctionTheory

set_option autoImplicit false

/-- The regular part of a neighbourhood after removing small closed disks. -/
def diskRegularRegion {ι : Type*} (W : Set ℂ) (c : ι → ℂ) (R : ι → ℝ) : Set ℂ :=
  W \ ⋃ i, closedBall (c i) (R i / 4)

/-- Compact collars that contain every overlap with a half-radius disk. -/
def diskOverlapCollars {ι : Type*} (c : ι → ℂ) (R : ι → ℝ) : Set ℂ :=
  ⋃ i, closedBall (c i) (R i / 2) \ ball (c i) (R i / 4)

theorem isOpen_diskRegularRegion {ι : Type*} [Finite ι]
    {W : Set ℂ} (hW : IsOpen W) (c : ι → ℂ) (R : ι → ℝ) :
    IsOpen (diskRegularRegion W c R) :=
  hW.sdiff (isClosed_iUnion_of_finite fun _ => isClosed_closedBall)

theorem closure_diskRegularRegion_subset {ι : Type*}
    {W U : Set ℂ} {c : ι → ℂ} {R : ι → ℝ}
    (hWU : closure W ⊆ U) (hR : ∀ i, 0 < R i) :
    closure (diskRegularRegion W c R) ⊆ U \ range c := by
  intro z hz
  refine ⟨hWU (closure_mono (show diskRegularRegion W c R ⊆ W from sdiff_subset) hz), ?_⟩
  rintro ⟨i, rfl⟩
  have hsub : diskRegularRegion W c R ⊆ (ball (c i) (R i / 4))ᶜ := by
    intro w hw hball
    exact hw.2 (mem_iUnion.mpr ⟨i, ball_subset_closedBall hball⟩)
  exact (closure_minimal hsub isOpen_ball.isClosed_compl hz)
    (mem_ball_self (div_pos (hR i) (by norm_num)))

theorem isCompact_closure_diskRegularRegion {ι : Type*}
    {W : Set ℂ} (hW : IsCompact (closure W)) (c : ι → ℂ) (R : ι → ℝ) :
    IsCompact (closure (diskRegularRegion W c R)) :=
  hW.of_isClosed_subset isClosed_closure (closure_mono sdiff_subset)

theorem isCompact_diskOverlapCollars {ι : Type*} [Finite ι]
    (c : ι → ℂ) (R : ι → ℝ) : IsCompact (diskOverlapCollars c R) :=
  isCompact_iUnion (fun i => (isCompact_closedBall (c i) (R i / 2)).diff isOpen_ball)

theorem diskOverlapCollars_subset {ι : Type*}
    {U : Set ℂ} {c : ι → ℂ} {R : ι → ℝ} (hR : ∀ i, 0 < R i)
    (hU : ∀ i, closedBall (c i) (R i) ⊆ U)
    (hdisj : Pairwise (fun i j => Disjoint (closedBall (c i) (R i))
      (closedBall (c j) (R j)))) :
    diskOverlapCollars c R ⊆ U \ range c := by
  intro z hz
  obtain ⟨i, hi, hiout⟩ := mem_iUnion.mp hz
  have hzi : z ∈ closedBall (c i) (R i) :=
    closedBall_subset_closedBall (by linarith [hR i]) hi
  refine ⟨hU i hzi, ?_⟩
  rintro ⟨j, hj⟩
  by_cases hij : i = j
  · subst j
    exact hiout (by simpa only [← hj] using mem_ball_self (div_pos (hR i) (by norm_num)))
  · exact Set.disjoint_left.mp (hdisj hij) hzi
      (by simpa only [← hj] using mem_closedBall_self (hR j).le)

theorem diskRegularRegion_union_halfBalls {ι : Type*}
    {W : Set ℂ} {c : ι → ℂ} {R : ι → ℝ} (hR : ∀ i, 0 < R i)
    (hW : ∀ i, closedBall (c i) (R i) ⊆ W) :
    diskRegularRegion W c R ∪ (⋃ i, ball (c i) (R i / 2)) = W := by
  apply subset_antisymm
  · rintro z (hz | hz)
    · exact hz.1
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact hW i (closedBall_subset_closedBall (by linarith [hR i])
        (ball_subset_closedBall hi))
  · intro z hz
    by_cases hhole : z ∈ ⋃ i, closedBall (c i) (R i / 4)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hhole
      exact Or.inr (mem_iUnion.mpr ⟨i, closedBall_subset_ball (by linarith [hR i]) hi⟩)
    · exact Or.inl ⟨hz, hhole⟩

theorem diskRegularRegion_inter_halfBall_subset_collars {ι : Type*}
    (W : Set ℂ) (c : ι → ℂ) (R : ι → ℝ) (i : ι) :
    diskRegularRegion W c R ∩ ball (c i) (R i / 2) ⊆ diskOverlapCollars c R := by
  intro z hz
  refine mem_iUnion.mpr ⟨i, ball_subset_closedBall hz.2, ?_⟩
  intro hi
  exact hz.1.2 (mem_iUnion.mpr ⟨i, ball_subset_closedBall hi⟩)

end FunctionTheory
