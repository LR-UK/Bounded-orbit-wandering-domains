import FunctionTheory.Conformal.TangentJordanDomain
import FunctionTheory.Conformal.InvertedDomain

open Set Metric Complex Bornology
open scoped Topology

namespace FunctionTheory

/-- Undoing inversion turns the image of a tangent disk into a compact
Jordan enclosure of the removed set. Only the designated tip may lie on
its boundary. -/
theorem tangent_disk_gives_compact_jordan_enclosure
    {E : Set ℂ} {G : ℂ → ℂ} {ξ c : ℂ} {t : ℝ}
    (hξ : ‖ξ‖ = 1) (ht : 0 < t) (htHalf : t < 1 / 2)
    (hGc : ContinuousOn G (insert ξ (ball (0 : ℂ) 1)))
    (hGi : InjOn G (insert ξ (ball (0 : ℂ) 1)))
    (hGd : DifferentiableOn ℂ G (ball 0 1))
    (hG0 : G 0 = 0) (hGξ : G ξ = c) (hc : c ≠ 0)
    (hGU : MapsTo G (ball 0 1) (invertedExterior E)) :
    let K := invertedExterior (G '' ball ((t : ℂ) * ξ) (1 - t))
    IsCompact K ∧ E ⊆ K ∧ E \ {c⁻¹} ⊆ interior K ∧
      TauCeti.IsJordanCurve (frontier K) ∧ c⁻¹ ∈ frontier K ∧
      frontier K \ {c⁻¹} ⊆ Eᶜ := by
  let B := ball ((t : ℂ) * ξ) (1 - t)
  let V := G '' B
  let K := invertedExterior V
  have ht1 : t < 1 := by linarith
  obtain ⟨hVo, _, hVb, hfr, hJ⟩ :=
    tangent_disk_image_is_bounded_jordan_domain hξ ht ht1 hGc hGi hGd
  have hBV := tangent_ball_subset_unitDisk hξ ht
  have h0V : (0 : ℂ) ∈ V := by
    rw [← hG0]
    exact mem_image_of_mem G (zero_mem_tangent_ball hξ ht htHalf)
  have hVU : V ⊆ invertedExterior E := by
    rintro _ ⟨w, hw, rfl⟩
    exact hGU (hBV hw)
  have hfrK : frontier K = (fun z : ℂ => z⁻¹) '' frontier V :=
    frontier_invertedExterior_of_bounded_open hVo hVb h0V
  have h0fr : (0 : ℂ) ∉ frontier V := fun h => (hVo.frontier_eq ▸ h).2 h0V
  have hclVU : closure V ⊆ insert c (invertedExterior E) := by
    rw [← TauCeti.image_closure_eq_closure_image isBounded_ball
      (show ContinuousOn G (closure B) from by
        dsimp only [B]
        rw [closure_ball _ (sub_pos.mpr ht1).ne']
        exact hGc.mono (tangent_closedBall_subset_insert_ball hξ ht ht1))
      (fun _ _ => rfl)]
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w ∈ insert ξ (ball (0 : ℂ) 1) := by
      rw [closure_ball _ (sub_pos.mpr ht1).ne'] at hw
      exact tangent_closedBall_subset_insert_ball hξ ht ht1 hw
    rcases hw' with rfl | hw
    · exact Or.inl hGξ
    · exact Or.inr (hGU hw)
  refine ⟨isCompact_invertedExterior_of_isOpen hVo h0V, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    · right
      intro hv
      rcases hVU hv with h | h
      · exact hz0 (inv_eq_zero.mp h)
      · exact h (by simpa using hz)
  · rintro z ⟨hz, hzc⟩
    by_cases hz0 : z = 0
    · subst z
      exact zero_mem_interior_invertedExterior hVb
    · rw [mem_interior_iff_mem_nhds, invertedExterior_mem_nhds_iff hz0]
      have hnot : z⁻¹ ∉ closure V := by
        intro hin
        rcases hclVU hin with he | hu
        · apply hzc
          simpa using congrArg Inv.inv he
        · rcases hu with hu | hu
          · exact hz0 (inv_eq_zero.mp hu)
          · exact hu (by simpa using hz)
      exact Filter.mem_of_superset (isClosed_closure.isOpen_compl.mem_nhds hnot)
        (compl_subset_compl.mpr subset_closure)
  · rw [hfrK]
    exact hJ.image (continuousOn_id.inv₀ (fun z hz he => h0fr (he ▸ hz))) inv_injective.injOn
  · rw [hfrK, hfr]
    exact ⟨c, ⟨ξ, tangency_point_mem_sphere hξ ht1, hGξ⟩, rfl⟩
  · rintro z ⟨hz, hzc⟩ hzE
    rw [hfrK] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rcases hclVU (frontier_subset_closure hw) with hwc | hwU
    · exact hzc (by simp [hwc])
    · rcases hwU with hw0 | hwE
      · exact h0fr (hw0 ▸ hw)
      · exact hwE hzE

end FunctionTheory
