import EremenkosConjecture.DiskMargins

open Set Metric

namespace EremenkosConjecture

noncomputable def AmbientDisk.unit : AmbientDisk := ⟨Homeomorph.refl ℂ⟩

theorem exists_ambientDisk_in_open {U : Set ℂ} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ D : AmbientDisk, D.carrier ⊆ U := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU a ha
  let E := AmbientDisk.unit.resize (δ / 2) (half_pos hδ)
  refine ⟨E.map (Homeomorph.addRight a), ?_⟩
  rw [E.carrier_map]
  rintro z ⟨w, hw, rfl⟩
  apply hball
  have hw' : ‖w‖ ≤ δ / 2 := (AmbientDisk.unit.mem_resize_carrier (half_pos hδ) w).mp hw
  change dist (w + a) a < δ
  rw [dist_eq_norm, add_sub_cancel_right]
  linarith

end EremenkosConjecture
