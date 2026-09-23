import EremenkosConjecture.AmbientExtension

open Set Metric Function
open scoped NNReal

namespace EremenkosConjecture

/-- A homeomorphism moving one point while fixing the complement of an open set. -/
def SupportedMove (U : Set ℂ) (a b : ℂ) : Prop :=
  ∃ H : ℂ ≃ₜ ℂ, H a = b ∧ ∀ z ∉ U, H z = z

theorem SupportedMove.refl (U : Set ℂ) (a : ℂ) : SupportedMove U a a :=
  ⟨Homeomorph.refl ℂ, rfl, fun _ _ => rfl⟩

theorem SupportedMove.trans {U : Set ℂ} {a b c : ℂ}
    (hab : SupportedMove U a b) (hbc : SupportedMove U b c) : SupportedMove U a c := by
  obtain ⟨H, hH, hfixH⟩ := hab
  obtain ⟨G, hG, hfixG⟩ := hbc
  refine ⟨H.trans G, ?_, ?_⟩
  · change G (H a) = c
    rw [hH, hG]
  · intro z hz
    change G (H z) = z
    rw [hfixH z hz, hfixG z hz]

theorem SupportedMove.symm {U : Set ℂ} {a b : ℂ}
    (h : SupportedMove U a b) : SupportedMove U b a := by
  obtain ⟨H, hH, hfix⟩ := h
  refine ⟨H.symm, by rw [← hH, H.symm_apply_apply], ?_⟩
  intro z hz
  apply H.injective
  rw [H.apply_symm_apply, hfix z hz]

theorem SupportedMove.mem {U : Set ℂ} {a b : ℂ}
    (h : SupportedMove U a b) (ha : a ∈ U) : b ∈ U := by
  obtain ⟨H, hH, hfix⟩ := h
  by_contra hb
  have hab : a = b := H.injective (hH.trans (hfix b hb).symm)
  exact hb (hab ▸ ha)

theorem exists_local_supportedMove {U : Set ℂ} (hU : IsOpen U) {a : ℂ} (ha : a ∈ U) :
    ∃ δ > 0, ∀ b ∈ ball a δ, SupportedMove U a b := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU a ha
  let C : ℝ≥0 := lipschitzExtensionConstant ℂ
  have hC : 0 < C := lipschitzExtensionConstant_pos ℂ
  let c : ℝ≥0 := (2 * C)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨(c : ℝ) * r, by positivity, ?_⟩
  intro b hb
  change dist b a < (c : ℝ) * r at hb
  rw [dist_eq_norm] at hb
  let f : ℂ → ℂ := fun z => if z = a then b else z
  have hsmall : LipschitzOnWith c (fun z => f z - z) (insert a Uᶜ) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    by_cases hxa : x = a
    · subst x
      by_cases hya : y = a
      · subst y
        simp
      · have hyU : y ∉ U := (mem_insert_iff.mp hy).resolve_left hya
        have hrle : r ≤ dist a y := by
          rw [dist_comm]
          exact le_of_not_gt (fun H => hyU (hrU H))
        simp only [f, ite_eq_left rfl, ite_eq_right hya, sub_self, dist_zero_right]
        exact (le_of_lt hb).trans (mul_le_mul_of_nonneg_left hrle c.coe_nonneg)
    · by_cases hya : y = a
      · subst y
        have hxU : x ∉ U := (mem_insert_iff.mp hx).resolve_left hxa
        have hrle : r ≤ dist x a := le_of_not_gt (fun H => hxU (hrU H))
        simp only [f, ite_eq_left rfl, ite_eq_right hxa, sub_self, dist_zero_left]
        exact (le_of_lt hb).trans (mul_le_mul_of_nonneg_left hrle c.coe_nonneg)
      · simp only [f, ite_eq_right hxa, ite_eq_right hya, sub_self, dist_self]
        positivity
  have happ : ApproximatesLinearOn f
      ((ContinuousLinearEquiv.refl ℝ ℂ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) (insert a Uᶜ) c := by
    apply LipschitzOnWith.approximatesLinearOn
    exact hsmall
  obtain ⟨H, hH⟩ := happ.exists_homeomorph_extension (Or.inr (by
    change C * c < ‖ContinuousLinearMap.id ℝ ℂ‖₊⁻¹
    rw [ContinuousLinearMap.nnnorm_id, inv_one]
    change C * (2 * C)⁻¹ < 1
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hC), one_mul]
    norm_num))
  refine ⟨H, ?_, ?_⟩
  · simpa only [f, ite_eq_left rfl] using (hH (mem_insert a Uᶜ)).symm
  · intro z hz
    have hza : z ≠ a := fun H => hz (H.symm ▸ ha)
    simpa only [f, ite_eq_right hza] using (hH (mem_insert_of_mem a hz)).symm

/-- Homeomorphisms supported in a connected open plane set act transitively on it. -/
theorem exists_supportedMove {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) : SupportedMove U a b := by
  let A : Set ℂ := {z | SupportedMove U a z}
  have hAU : A ⊆ U := fun _ h => h.mem ha
  have haA : a ∈ A := SupportedMove.refl U a
  have hAopen : IsOpen A := by
    apply Metric.isOpen_iff.mpr
    intro z hz
    obtain ⟨δ, hδ, hlocal⟩ := exists_local_supportedMove hU (hAU hz)
    exact ⟨δ, hδ, fun w hw => hz.trans (hlocal w hw)⟩
  have hBopen : IsOpen (U \ A) := by
    apply Metric.isOpen_iff.mpr
    intro z hz
    obtain ⟨δ, hδ, hlocal⟩ := exists_local_supportedMove hU hz.1
    refine ⟨δ, hδ, fun w hw => ?_⟩
    have hmove := hlocal w hw
    exact ⟨hmove.mem hz.1, fun hwA => hz.2 (hwA.trans hmove.symm)⟩
  have hsub : U ⊆ A ∪ (U \ A) := by intro z hz; by_cases hzA : z ∈ A <;> simp_all
  have H := hconn.subset_left_of_subset_union hAopen hBopen
    (disjoint_sdiff_right) hsub ⟨a, ha, haA⟩
  exact H hb

end EremenkosConjecture
