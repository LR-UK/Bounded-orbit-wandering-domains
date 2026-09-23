import ComplexDynamics.Bungee
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Dynamical sets under a homeomorphism of the plane -/

open Function Filter Set Metric
open scoped Topology Uniformity

namespace ComplexDynamics

noncomputable def conjugate (H : ℂ ≃ₜ ℂ) (f : ℂ → ℂ) : ℂ → ℂ := H ∘ f ∘ H.symm

theorem iterate_conjugate (H : ℂ ≃ₜ ℂ) (f : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    ((conjugate H f)^[n]) z = H ((f^[n]) (H.symm z)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iterate_succ_apply', ih, iterate_succ_apply']
      simp only [conjugate, comp_apply, H.symm_apply_apply]

@[simp] theorem conjugate_symm (H : ℂ ≃ₜ ℂ) (f : ℂ → ℂ) :
    conjugate H.symm (conjugate H f) = f := by
  funext z
  simp only [conjugate, comp_apply, Homeomorph.symm_symm, H.symm_apply_apply, H.apply_symm_apply]

theorem mapsTo_escapingSet_conjugate (H : ℂ ≃ₜ ℂ) (f : ℂ → ℂ) :
    MapsTo H (escapingSet f) (escapingSet (conjugate H f)) := by
  intro z hz
  have hH : Tendsto H (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) := by
    rw [Metric.cobounded_eq_cocompact]
    exact H.map_cocompact.le
  have h := tendsto_norm_atTop_iff_cobounded.mpr
    (hH.comp (tendsto_norm_atTop_iff_cobounded.mp hz))
  simpa only [escapingSet, mem_setOf_eq, iterate_conjugate, H.symm_apply_apply, comp_apply] using h

theorem mem_escapingSet_conjugate_iff (H : ℂ ≃ₜ ℂ) (f : ℂ → ℂ) (z : ℂ) :
    H z ∈ escapingSet (conjugate H f) ↔ z ∈ escapingSet f := by
  constructor
  · intro hz
    simpa only [conjugate_symm, H.symm_apply_apply] using mapsTo_escapingSet_conjugate H.symm (conjugate H f) hz
  · exact fun hz => mapsTo_escapingSet_conjugate H f hz

theorem mapsTo_boundedOrbitSet_conjugate (H : ℂ ≃ₜ ℂ) (f : ℂ → ℂ) :
    MapsTo H (boundedOrbitSet f) (boundedOrbitSet (conjugate H f)) := by
  rintro z ⟨R, hR⟩
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : ℂ) R).image H.continuous).isBounded.exists_norm_le
  refine ⟨M, fun n => ?_⟩
  rw [iterate_conjugate, H.symm_apply_apply]
  exact hM _ (mem_image_of_mem H (mem_closedBall_zero_iff.mpr (hR n)))

theorem mem_boundedOrbitSet_conjugate_iff (H : ℂ ≃ₜ ℂ) (f : ℂ → ℂ) (z : ℂ) :
    H z ∈ boundedOrbitSet (conjugate H f) ↔ z ∈ boundedOrbitSet f := by
  constructor
  · intro hz
    simpa only [conjugate_symm, H.symm_apply_apply] using mapsTo_boundedOrbitSet_conjugate H.symm (conjugate H f) hz
  · exact fun hz => mapsTo_boundedOrbitSet_conjugate H f hz

theorem mem_bungeeSet_conjugate_iff (H : ℂ ≃ₜ ℂ) (f : ℂ → ℂ) (z : ℂ) :
    H z ∈ bungeeSet (conjugate H f) ↔ z ∈ bungeeSet f := by
  simp only [mem_bungeeSet_iff, mem_boundedOrbitSet_conjugate_iff, mem_escapingSet_conjugate_iff]

theorem normalSequence_conjugate (H : ℂ ≃ₜ ℂ) (f : ℂ → ℂ) {U : Set ℂ}
    (hnormal : IsNormalSequenceOn (sphericalIterate f) U) :
    IsNormalSequenceOn (sphericalIterate (conjugate H f)) (H '' U) := by
  intro φ hφ
  obtain ⟨ψ, hψ, g, hg⟩ := hnormal φ hφ
  let i : H '' U → U := fun z => ⟨H.symm z, by
    obtain ⟨w, hw, he⟩ := z.property
    simpa only [← he, H.symm_apply_apply] using hw⟩
  have hi : Continuous i := (H.symm.continuous.comp continuous_subtype_val).subtype_mk _
  have hH : UniformContinuous H.onePointCongr :=
    CompactSpace.uniformContinuous_of_continuous H.onePointCongr.continuous
  refine ⟨ψ, hψ, H.onePointCongr ∘ g ∘ i, ?_⟩
  have hconv := hH.comp_tendstoLocallyUniformly (hg.comp i hi)
  convert hconv using 1
  funext n z
  change ((conjugate H f)^[φ (ψ n)] (z : ℂ) : RiemannSphere) =
    (H ((f^[φ (ψ n)]) (H.symm z)) : RiemannSphere)
  rw [iterate_conjugate]

theorem mapsTo_fatouSet_conjugate (H : ℂ ≃ₜ ℂ) (f : ℂ → ℂ) :
    MapsTo H (fatouSet f) (fatouSet (conjugate H f)) := by
  rintro z ⟨U, hU, hz, hnormal⟩
  exact ⟨H '' U, H.isOpenMap _ hU, mem_image_of_mem H hz, normalSequence_conjugate H f hnormal⟩

theorem mem_fatouSet_conjugate_iff (H : ℂ ≃ₜ ℂ) (f : ℂ → ℂ) (z : ℂ) :
    H z ∈ fatouSet (conjugate H f) ↔ z ∈ fatouSet f := by
  constructor
  · intro hz
    simpa only [conjugate_symm, H.symm_apply_apply] using mapsTo_fatouSet_conjugate H.symm (conjugate H f) hz
  · exact fun hz => mapsTo_fatouSet_conjugate H f hz

theorem mem_juliaSet_conjugate_iff (H : ℂ ≃ₜ ℂ) (f : ℂ → ℂ) (z : ℂ) :
    H z ∈ juliaSet (conjugate H f) ↔ z ∈ juliaSet f := by
  simp only [juliaSet, mem_compl_iff, mem_fatouSet_conjugate_iff]

private theorem image_eq_of_mem_iff (H : ℂ ≃ₜ ℂ) (A B : Set ℂ)
    (h : ∀ z, H z ∈ B ↔ z ∈ A) : H '' A = B := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (h w).mpr hw
  · intro hz
    exact ⟨H.symm z, (h (H.symm z)).mp (by simpa only [H.apply_symm_apply] using hz), H.apply_symm_apply z⟩

theorem image_escapingSet_conjugate (H : ℂ ≃ₜ ℂ) (f : ℂ → ℂ) :
    H '' escapingSet f = escapingSet (conjugate H f) :=
  image_eq_of_mem_iff H _ _ (mem_escapingSet_conjugate_iff H f)

theorem image_bungeeSet_conjugate (H : ℂ ≃ₜ ℂ) (f : ℂ → ℂ) :
    H '' bungeeSet f = bungeeSet (conjugate H f) :=
  image_eq_of_mem_iff H _ _ (mem_bungeeSet_conjugate_iff H f)

theorem image_juliaSet_conjugate (H : ℂ ≃ₜ ℂ) (f : ℂ → ℂ) :
    H '' juliaSet f = juliaSet (conjugate H f) :=
  image_eq_of_mem_iff H _ _ (mem_juliaSet_conjugate_iff H f)

end ComplexDynamics
