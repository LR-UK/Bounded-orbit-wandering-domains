import EremenkosConjecture.FinitePath
import Schoenflies.JordanClosed

/-! # Finite chains of overlapping squares around a continuum -/

open Set Metric Schoenflies
open scoped Topology

namespace EremenkosConjecture

theorem exists_square_chain_cover {K U : Set Plane}
    (hK : IsCompact K) (hconn : IsConnected K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (r : ℝ) (N : ℕ) (c : ℕ → Plane), 0 < r ∧
      (∀ j < N, Plane.supDist (c j) (c (j + 1)) < r) ∧
      (∀ x ∈ K, ∃ j ≤ N, x ∈ Plane.openSquare (c j) r) ∧
      ∀ j ≤ N, Plane.closedSquare (c j) r ⊆ U := by
  classical
  obtain ⟨δ, hδ, htube⟩ := hK.exists_thickening_subset_open hU hKU
  let r := δ / 8
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨a, ha⟩ := hconn.nonempty
  let V := connectedComponentIn (thickening r K) a
  have hKV : K ⊆ V := hconn.isPreconnected.subset_connectedComponentIn ha
    (self_subset_thickening hr K)
  have hVo : IsOpen V := isOpen_thickening.connectedComponentIn
  have hVc : IsConnected V := isConnected_connectedComponentIn_iff.mpr
    (self_subset_thickening hr K ha)
  have hVp : IsPathConnected V := hVo.isConnected_iff_isPathConnected.mp hVc
  have hcover : K ⊆ ⋃ x : K, ball (x : Plane) (r / 4) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (by positivity)⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => ball (x : Plane) (r / 4))
    (fun _ => isOpen_ball) hcover
  obtain ⟨γ, hγ, hvisit⟩ := exists_loop_through_finset hVp (hKV ha)
    (s.image Subtype.val) (by
      intro x hx
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
      exact hKV y.property)
  obtain ⟨N, hN, hmesh⟩ := exists_mesh γ.continuous_extend.continuousOn
    (show 0 < r / 4 by positivity) 1 zero_lt_one
  simp only [one_mul] at hmesh
  let c : ℕ → Plane := fun j => γ.extend (sample N j)
  have hcV (j : ℕ) : c j ∈ V := hγ (by rw [← γ.extend_range]; exact mem_range_self _)
  refine ⟨r, N, c, hr, ?_, ?_, ?_⟩
  · intro j hj
    have H := hmesh j hj (sample N (j + 1)) ⟨sample_mono (by omega), le_rfl⟩
    have hd : dist (c j) (c (j + 1)) < r / 4 := by simpa only [c, dist_comm] using H
    exact (Plane.supDist_eq_dist_le _ _).trans_lt (hd.trans (by linarith))
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
    have hyγ : (y : Plane) ∈ range γ := hvisit (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
    obtain ⟨t, ht⟩ := hyγ
    obtain ⟨j, hj, htj⟩ := exists_mem_Icc_sample hN t.property
    have H := hmesh j hj t htj
    have hyc : dist (y : Plane) (c j) < r / 4 := by
      simpa only [c, γ.extend_extends' t, ht] using H
    refine ⟨j, hj.le, ?_⟩
    change Plane.supDist x (c j) < r
    have hd := dist_triangle x y (c j)
    exact (Plane.supDist_eq_dist_le _ _).trans_lt (by have := mem_ball.mp hxy; linarith)
  · intro j hj w hw
    have hc : c j ∈ thickening r K := connectedComponentIn_subset _ _ (hcV j)
    obtain ⟨x, hx, hcx⟩ := mem_thickening_iff.mp hc
    have hwc : dist w (c j) < 2 * r := by
      have H := Plane.closedSquare_subset_ball (c := c j) (show 0 < 2 * r by positivity)
      apply H
      simpa using hw
    apply htube
    apply mem_thickening_iff.mpr
    refine ⟨x, hx, ?_⟩
    have H := dist_triangle w (c j) x
    dsimp [r] at *
    linarith

end EremenkosConjecture
