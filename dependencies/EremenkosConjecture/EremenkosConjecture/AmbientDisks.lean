import EremenkosConjecture.RadialDomains
import EremenkosConjecture.PointMoving

open Set Metric Function

namespace EremenkosConjecture

/-- A closed topological disk together with a homeomorphism of the whole plane. -/
structure AmbientDisk where
  chart : ℂ ≃ₜ ℂ

namespace AmbientDisk

def carrier (D : AmbientDisk) : Set ℂ := D.chart '' closedBall 0 1

def inside (D : AmbientDisk) : Set ℂ := D.chart '' ball 0 1

theorem mem_carrier (D : AmbientDisk) (z : ℂ) : z ∈ D.carrier ↔ ‖D.chart.symm z‖ ≤ 1 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [D.chart.symm_apply_apply, mem_closedBall, dist_zero_right] using hw
  · intro hz
    exact ⟨D.chart.symm z, mem_closedBall_zero_iff.mpr hz, D.chart.apply_symm_apply z⟩

theorem mem_inside (D : AmbientDisk) (z : ℂ) : z ∈ D.inside ↔ ‖D.chart.symm z‖ < 1 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [D.chart.symm_apply_apply, mem_ball, dist_zero_right] using hw
  · intro hz
    exact ⟨D.chart.symm z, mem_ball_zero_iff.mpr hz, D.chart.apply_symm_apply z⟩

theorem compact (D : AmbientDisk) : IsCompact D.carrier :=
  (isCompact_closedBall (0 : ℂ) 1).image D.chart.continuous

theorem open_inside (D : AmbientDisk) : IsOpen D.inside := D.chart.isOpenMap _ isOpen_ball

theorem interior_carrier (D : AmbientDisk) : interior D.carrier = D.inside := by
  rw [carrier, ← D.chart.image_interior, interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
  rfl

theorem closure_inside (D : AmbientDisk) : closure D.inside = D.carrier := by
  rw [inside, ← D.chart.image_closure, closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
  rfl

theorem inside_subset (D : AmbientDisk) : D.inside ⊆ D.carrier := image_mono ball_subset_closedBall

theorem connected (D : AmbientDisk) : IsConnected D.carrier :=
  ((convex_closedBall (0 : ℂ) 1).isConnected ⟨0, by simp⟩).image D.chart D.chart.continuous.continuousOn

theorem connected_inside (D : AmbientDisk) : IsConnected D.inside :=
  ((convex_ball (0 : ℂ) 1).isConnected ⟨0, by simp⟩).image D.chart D.chart.continuous.continuousOn

theorem full (D : AmbientDisk) : IsConnected D.carrierᶜ := by
  apply isConnected_compl_image_homeomorph D.chart
  have H := isConnected_exterior 1 (by norm_num)
  convert H using 1
  ext z
  simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le, mem_setOf_eq]

noncomputable def map (D : AmbientDisk) (H : ℂ ≃ₜ ℂ) : AmbientDisk := ⟨D.chart.trans H⟩

theorem carrier_map (D : AmbientDisk) (H : ℂ ≃ₜ ℂ) : (D.map H).carrier = H '' D.carrier := by
  rw [carrier, carrier, image_image]
  rfl

theorem inside_map (D : AmbientDisk) (H : ℂ ≃ₜ ℂ) : (D.map H).inside = H '' D.inside := by
  rw [inside, inside, image_image]
  rfl

/-- The remaining open land inside a disk is connected after removing a full compact set. -/
theorem pathConnected_sdiff (D : AmbientDisk) {A : Set ℂ} (hA : IsCompact A)
    (hfull : IsConnected Aᶜ) (hAD : A ⊆ D.inside) : IsPathConnected (D.inside \ A) := by
  let B := D.chart.symm '' A
  have hBc : IsCompact B := hA.image D.chart.symm.continuous
  have hBf : IsConnected Bᶜ := isConnected_compl_image_homeomorph D.chart.symm hfull
  have hBD : B ⊆ ball (0 : ℂ) 1 := by
    rintro z ⟨w, hw, rfl⟩
    exact mem_ball_zero_iff.mpr ((mem_inside D w).mp (hAD hw))
  have H := (isPathConnected_ball_sdiff_full hBc hBf (by norm_num) hBD).image D.chart.continuous
  have heq : D.chart '' (ball (0 : ℂ) 1 \ B) = D.inside \ A := by
    rw [Set.image_sdiff D.chart.injective]
    change D.inside \ (D.chart '' (D.chart.symm '' A)) = D.inside \ A
    rw [← image_comp, show D.chart ∘ D.chart.symm = id from funext D.chart.apply_symm_apply, image_id]
  rwa [heq] at H

end AmbientDisk

end EremenkosConjecture
