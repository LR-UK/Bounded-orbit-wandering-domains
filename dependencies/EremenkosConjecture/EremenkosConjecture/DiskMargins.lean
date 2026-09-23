import EremenkosConjecture.AmbientDisks

open Set Metric Function

namespace EremenkosConjecture

theorem dist_radialRetraction {r : ℝ} (hr : 0 < r) (z : ℂ) :
    dist z (radialRetraction r z) = max 0 (‖z‖ - r) := by
  rcases le_total ‖z‖ r with hz | hz
  · rw [radialRetraction_eq_self hr hz, dist_self, max_eq_left (sub_nonpos.mpr hz)]
  · have hzn : 0 < ‖z‖ := hr.trans_le hz
    have hcoef : 0 ≤ 1 - r / ‖z‖ := sub_nonneg.mpr ((div_le_one hzn).mpr hz)
    rw [radialRetraction, max_eq_right hz, dist_eq_norm]
    rw [show z - (r / ‖z‖) • z = (1 - r / ‖z‖) • z by rw [sub_smul, one_smul]]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef, max_eq_right (sub_nonneg.mpr hz)]
    field_simp

theorem exists_outer_radius {U : Set ℂ} (hU : IsOpen U) (hball : closedBall 0 1 ⊆ U) :
    ∃ r : ℝ, 1 < r ∧ closedBall 0 r ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open hU hball
  refine ⟨1 + δ / 2, by linarith, ?_⟩
  intro z hz
  apply hδU
  refine mem_thickening_iff.mpr ⟨radialRetraction 1 z, ?_, ?_⟩
  · exact mem_closedBall_zero_iff.mpr (norm_radialRetraction_le (by norm_num) z)
  · rw [dist_radialRetraction (by norm_num), max_lt_iff]
    have H : ‖z‖ ≤ 1 + δ / 2 := mem_closedBall_zero_iff.mp hz
    exact ⟨hδ, by linarith⟩

namespace AmbientDisk

noncomputable def resize (D : AmbientDisk) (r : ℝ) (hr : 0 < r) : AmbientDisk :=
  ⟨(Homeomorph.mulLeft₀ (r : ℂ) (by exact_mod_cast ne_of_gt hr)).trans D.chart⟩

theorem mem_resize_carrier (D : AmbientDisk) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    z ∈ (D.resize r hr).carrier ↔ ‖D.chart.symm z‖ ≤ r := by
  rw [mem_carrier]
  change ‖(Homeomorph.mulLeft₀ (r : ℂ) _).symm (D.chart.symm z)‖ ≤ 1 ↔ _
  rw [Homeomorph.mulLeft₀_symm_apply, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr, mul_comm, ← div_eq_mul_inv, div_le_one hr]

theorem mem_resize_inside (D : AmbientDisk) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    z ∈ (D.resize r hr).inside ↔ ‖D.chart.symm z‖ < r := by
  rw [mem_inside]
  change ‖(Homeomorph.mulLeft₀ (r : ℂ) _).symm (D.chart.symm z)‖ < 1 ↔ _
  rw [Homeomorph.mulLeft₀_symm_apply, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr, mul_comm, ← div_eq_mul_inv, div_lt_one hr]

theorem exists_larger (D : AmbientDisk) {U : Set ℂ} (hU : IsOpen U) (hDU : D.carrier ⊆ U) :
    ∃ E : AmbientDisk, D.carrier ⊆ E.inside ∧ E.carrier ⊆ U ∧
      (E.inside \ D.carrier).Nonempty := by
  obtain ⟨r, hr, hball⟩ := exists_outer_radius (hU.preimage D.chart.continuous)
    (fun z hz => hDU ⟨z, hz, rfl⟩)
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  refine ⟨D.resize r hr0, ?_, ?_, ?_⟩
  · intro z hz
    exact (D.mem_resize_inside hr0 z).mpr (((D.mem_carrier z).mp hz).trans_lt hr)
  · intro z hz
    have H := hball (mem_closedBall_zero_iff.mpr ((D.mem_resize_carrier hr0 z).mp hz))
    simpa only [mem_preimage, D.chart.apply_symm_apply] using H
  · let s := (1 + r) / 2
    have hs0 : 0 < s := by dsimp [s]; linarith
    have hsnorm : ‖(s : ℂ)‖ = s := by simp [Complex.norm_real, abs_of_pos hs0]
    refine ⟨D.chart (s : ℂ), ?_, ?_⟩
    · rw [D.mem_resize_inside hr0, D.chart.symm_apply_apply, hsnorm]
      dsimp [s]
      linarith
    · rw [D.mem_carrier, D.chart.symm_apply_apply, hsnorm]
      dsimp [s]
      linarith

theorem exists_smaller (D : AmbientDisk) {A : Set ℂ} (hA : IsCompact A) (hAD : A ⊆ D.inside) :
    ∃ E : AmbientDisk, A ⊆ E.inside ∧ E.carrier ⊆ D.inside ∧
      (D.inside \ E.carrier).Nonempty := by
  obtain ⟨r, hr0, hr, hball⟩ := exists_inner_radius (hA.image D.chart.symm.continuous)
    (by norm_num : (0 : ℝ) < 1) (by
      rintro z ⟨w, hw, rfl⟩
      exact mem_ball_zero_iff.mpr ((D.mem_inside w).mp (hAD hw)))
  refine ⟨D.resize r hr0, ?_, ?_, ?_⟩
  · intro z hz
    exact (D.mem_resize_inside hr0 z).mpr (mem_ball_zero_iff.mp (hball ⟨z, hz, rfl⟩))
  · intro z hz
    exact (D.mem_inside z).mpr (((D.mem_resize_carrier hr0 z).mp hz).trans_lt hr)
  · let s := (r + 1) / 2
    have hs0 : 0 < s := by dsimp [s]; positivity
    have hsnorm : ‖(s : ℂ)‖ = s := by simp [Complex.norm_real, abs_of_pos hs0]
    refine ⟨D.chart (s : ℂ), ?_, ?_⟩
    · rw [D.mem_inside, D.chart.symm_apply_apply, hsnorm]
      dsimp [s]
      linarith
    · rw [D.mem_resize_carrier hr0, D.chart.symm_apply_apply, hsnorm]
      dsimp [s]
      linarith

end AmbientDisk

end EremenkosConjecture
