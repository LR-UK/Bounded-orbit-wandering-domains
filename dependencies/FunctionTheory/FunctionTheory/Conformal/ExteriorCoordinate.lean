import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic

open Set Metric Complex Bornology
open scoped Topology

namespace FunctionTheory

/-- The spherical exterior in the coordinate `z ↦ 1/z`. Zero represents
infinity, so it is explicitly included. The pole belongs to the removed set. -/
def invertedExterior (K : Set ℂ) : Set ℂ := {w | w = 0 ∨ w⁻¹ ∉ K}

theorem invertedExterior_eq_insert_image (K : Set ℂ) :
    invertedExterior K = insert 0 ((fun z : ℂ => z⁻¹) '' Kᶜ) := by
  ext w
  constructor
  · rintro (rfl | hw)
    · exact mem_insert 0 _
    · exact mem_insert_of_mem 0 ⟨w⁻¹, hw, inv_inv w⟩
  · rintro (rfl | ⟨z, hz, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (by simpa using hz)

theorem isOpen_invertedExterior {K : Set ℂ} (hK : IsCompact K) :
    IsOpen (invertedExterior K) := by
  apply isOpen_iff_mem_nhds.mpr
  intro w hw
  by_cases hw0 : w = 0
  · subst w
    obtain ⟨M, hM, hbound⟩ := hK.isBounded.exists_pos_norm_le
    have hM1 : 0 < M + 1 := by linarith
    apply Metric.mem_nhds_iff.mpr
    refine ⟨1 / (M + 1), by positivity, ?_⟩
    intro z hz
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    · right
      intro hzK
      have hsmall : ‖z‖ < 1 / (M + 1) := by
        simpa only [mem_ball, dist_zero_right] using hz
      have hprod : ‖z‖ * (M + 1) < 1 := (lt_div_iff₀ hM1).mp hsmall
      have hle := mul_le_mul_of_nonneg_right (hbound _ hzK) (norm_nonneg z)
      rw [norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)] at hle
      nlinarith [norm_nonneg z]
  · have hwK : w⁻¹ ∉ K := hw.resolve_left hw0
    have hpre : {z : ℂ | z⁻¹ ∉ K} ∈ 𝓝 w :=
      (continuousAt_inv₀ hw0).preimage_mem_nhds (hK.isClosed.isOpen_compl.mem_nhds hwK)
    exact Filter.mem_of_superset hpre (fun z hz => Or.inr hz)

theorem zero_mem_closure_inv_exterior {K : Set ℂ} (hK : IsBounded K) :
    (0 : ℂ) ∈ closure ((fun z : ℂ => z⁻¹) '' Kᶜ) := by
  obtain ⟨M, hM, hbound⟩ := hK.exists_pos_norm_le
  rw [Metric.mem_closure_iff]
  intro ε hε
  let t := M + ε⁻¹ + 1
  have ht : 0 < t := by dsimp [t]; positivity
  have htM : M < t := by dsimp [t]; linarith [inv_pos.mpr hε]
  have htε : ε⁻¹ < t := by dsimp [t]; linarith
  have hnot : (t : ℂ) ∉ K := by
    intro h
    have hb := hbound _ h
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] at hb
    exact not_le.mpr htM hb
  refine ⟨(t : ℂ)⁻¹, ⟨(t : ℂ), hnot, rfl⟩, ?_⟩
  have hi : t⁻¹ < ε := by
    simpa only [one_div, inv_inv] using
      one_div_lt_one_div_of_lt (inv_pos.mpr hε) htε
  simpa only [dist_comm (0 : ℂ), dist_zero_right, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ht] using hi

/-- A full compact set has a connected spherical exterior, expressed in one
ordinary complex coordinate chart. The added point is the image of infinity. -/
theorem isConnected_invertedExterior {K : Set ℂ}
    (hK : IsCompact K) (hfull : IsConnected Kᶜ) (h0 : (0 : ℂ) ∈ K) :
    IsConnected (invertedExterior K) := by
  have hc : ContinuousOn (fun z : ℂ => z⁻¹) Kᶜ := by
    apply continuousOn_id.inv₀
    intro z hz heq
    change z = 0 at heq
    exact hz (heq.symm ▸ h0)
  have hconn := hfull.image (fun z : ℂ => z⁻¹) hc
  rw [invertedExterior_eq_insert_image]
  exact hconn.subset_closure (subset_insert _ _)
    (insert_subset (zero_mem_closure_inv_exterior hK.isBounded) subset_closure)

/-- Approaching the pole in a punctured set makes its inverted image unbounded. -/
theorem not_isBounded_inv_image_of_zero_mem_closure {S : Set ℂ}
    (hcl : (0 : ℂ) ∈ closure S) (h0 : (0 : ℂ) ∉ S) :
    ¬ IsBounded ((fun z : ℂ => z⁻¹) '' S) := by
  intro hb
  obtain ⟨M, hM, hbound⟩ := hb.exists_pos_norm_le
  have hM1 : 0 < M + 1 := by linarith
  obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.mp hcl (1 / (M + 1)) (by positivity)
  have hz0 : z ≠ 0 := fun heq => h0 (heq ▸ hz)
  have hsmall : ‖z‖ < 1 / (M + 1) := by
    simpa only [dist_comm (0 : ℂ), dist_zero_right] using hdist
  have hprod : ‖z‖ * (M + 1) < 1 := (lt_div_iff₀ hM1).mp hsmall
  have hle := mul_le_mul_of_nonneg_right (hbound _ ⟨z, hz, rfl⟩) (norm_nonneg z)
  rw [norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)] at hle
  nlinarith [norm_nonneg z]

end FunctionTheory
