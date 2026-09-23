/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.TrappedSimpleConnectivity
import BoundedWanderingDomains.OmittedPairCompactness

open Set Metric Function Filter
open scoped Topology

namespace AreaDeficit

/-- Schottky's estimate gives a bounded neighbourhood from a bounded marked
orbit in an open wandering component. No bound on whole components is used. -/
theorem bounded_point_mem_trapped_interior {f : ℂ → ℂ} {U : ℕ → Set ℂ} {z : ℂ}
    (hf : Differentiable ℂ f) (hU : IsOpen (U 0)) (hz : z ∈ U 0)
    (hforward : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m)))
    (hbound : ∃ R : ℝ, ∀ n : ℕ, ‖(f^[n]) z‖ ≤ R) :
    ∃ R > 0, z ∈ interior (trappedSet f (ball 0 R)) := by
  obtain ⟨R, hR⟩ := hbound
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU z hz
  let b : ℂ := z + (δ / 2 : ℝ)
  have hbz : b ≠ z := by
    dsimp [b]
    simpa using (show (δ / 2 : ℂ) ≠ 0 by exact_mod_cast (by linarith : δ / 2 ≠ 0))
  have hbU : b ∈ U 0 := by
    apply hδU
    rw [mem_ball_iff_norm]
    simp only [b, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < δ / 2)]
    linarith
  have hit : ∀ n, MapsTo (f^[n]) (U 0) (U n) := by
    intro n
    induction n with
    | zero => exact mapsTo_id _
    | succ n ih => simpa only [iterate_succ'] using (hforward n).comp ih
  let q : ℕ → ℂ → ℂ := fun n w => ((f^[n + 1]) w - z) / (b - z)
  have hba : b - z ≠ 0 := sub_ne_zero.mpr hbz
  have hqa : ∀ n, AnalyticOnNhd ℂ (q n) (ball z δ) := by
    intro n
    exact ((((hf.iterate (n + 1)).differentiableOn.analyticOnNhd isOpen_univ).sub
      analyticOnNhd_const).div_const).mono (subset_univ _)
  have hq0 : ∀ n w, w ∈ ball z δ → q n w ≠ 0 := by
    intro n w hw he
    have he' : (f^[n + 1]) w = z := sub_eq_zero.mp (((div_eq_zero_iff).mp he).resolve_right hba)
    exact disjoint_left.mp (hdis (by omega : n + 1 ≠ 0)) (he' ▸ hit (n + 1) (hδU hw)) hz
  have hq1 : ∀ n w, w ∈ ball z δ → q n w ≠ 1 := by
    intro n w hw he
    have he' : (f^[n + 1]) w = b := sub_left_injective ((div_eq_one_iff_eq hba).mp he)
    exact disjoint_left.mp (hdis (by omega : n + 1 ≠ 0)) (he' ▸ hit (n + 1) (hδU hw)) hbU
  let C := (R + ‖z‖) / ‖b - z‖
  have hbase : ∀ n, ‖q n z‖ ≤ C := by
    intro n
    dsimp [q, C]
    rw [norm_div]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    have H : ‖(f^[n]) (f z)‖ ≤ R := by simpa only [iterate_succ_apply] using hR (n + 1)
    linarith [norm_sub_le ((f^[n]) (f z)) z]
  let M := FunctionTheory.schottkyZeroOneMajorant C (1 / 2)
  let B := max (δ + ‖z‖) (‖b - z‖ * M + ‖z‖)
  have hB : ∀ n w, w ∈ ball z (δ / 2) → ‖(f^[n]) w‖ ≤ B := by
    intro n w hw
    cases n with
    | zero =>
        apply le_trans _ (le_max_left _ _)
        have H' : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by simpa only [add_comm] using norm_le_insert' w z
        have hw' := mem_ball_iff_norm.mp hw
        simp only [iterate_zero_apply]
        linarith
    | succ n =>
        have H := FunctionTheory.norm_le_schottkyZeroOneMajorant_on_disc hδ
          (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)
          (hqa n) (hq0 n) (hq1 n) (hbase n)
          (z := w) (by have := (mem_ball_iff_norm.mp hw).le; linarith)
        have he : (f^[n + 1]) w = (b - z) * q n w + z := by dsimp [q]; field_simp; ring
        apply le_trans _ (le_max_right _ _)
        rw [he]
        exact (norm_add_le _ _).trans (by rw [norm_mul]; gcongr)
  refine ⟨B + 1, ?_, ?_⟩
  · have := le_max_left (δ + ‖z‖) (‖b - z‖ * M + ‖z‖)
    dsimp [B]
    linarith [norm_nonneg z]
  · apply mem_interior_iff_mem_nhds.mpr
    apply mem_of_superset (ball_mem_nhds z (by linarith : 0 < δ / 2))
    intro w hw n
    exact mem_ball_zero_iff.mpr (lt_of_le_of_lt (hB n w hw) (by linarith))

/-- For an open map, open- and closed-disc trapped sets have the same interior. -/
theorem trapped_ball_interior_eq_closed {f : ℂ → ℂ}
    (hf : IsOpenMap f) {R : ℝ} (hR : R ≠ 0) :
    interior (trappedSet f (ball 0 R)) = interior (trappedSet f (closedBall 0 R)) := by
  apply Subset.antisymm
  · exact interior_mono (fun x hx n => ball_subset_closedBall (hx n))
  · apply isOpen_interior.subset_interior_iff.mpr
    intro x hx n
    have hop : ∀ n : ℕ, IsOpenMap (f^[n]) := by
      intro n
      induction n with
      | zero => intro S hS; simpa using hS
      | succ n ih => simpa only [iterate_succ'] using hf.comp ih
    have him : (f^[n]) '' interior (trappedSet f (closedBall 0 R)) ⊆ closedBall 0 R := by
      rintro _ ⟨w, hw, rfl⟩
      exact interior_subset hw n
    have H := ((hop n) _ isOpen_interior).subset_interior_iff.mpr him ⟨x, hx, rfl⟩
    simpa only [interior_closedBall (0 : ℂ) hR] using H

end AreaDeficit
