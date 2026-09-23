import EremenkosConjecture.RayOrbitProperty
import EremenkosConjecture.RayBarrierStability

/-! # Choosing common tolerances for a ray-construction step -/

open Set Metric Function
open scoped NNReal

namespace EremenkosConjecture

open Scaffolding

private theorem exists_common_positive_bound {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) : ∃ r : ℝ, 0 < r ∧ ∀ i, r ≤ d i := by
  classical
  have hfinite (s : Finset ι) : ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, r ≤ d i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i s hi ih =>
        obtain ⟨r, hr, hbound⟩ := ih
        refine ⟨min r (d i), lt_min hr (hd i), ?_⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hbound k hk)
  obtain ⟨r, hr, hbound⟩ := hfinite Finset.univ
  exact ⟨r, hr, fun i => hbound i (Finset.mem_univ i)⟩

namespace RayReference

variable {j : ℕ} {S : RayStage j} {R : RayReturnChannel S.f j S.a S.b}
    (P : RayReference S R)

theorem exists_iterate_tolerance {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ F : ℂ → ℂ,
      (∀ z ∈ P.controlSet, dist (F z) (P.g z) < δ) →
      ∀ k ≤ returnTime (j + 1), ∀ z ∈ R.buffer,
        dist ((F^[k]) z) ((P.g^[k]) z) < ε := by
  obtain ⟨δ, hδ, Hδ⟩ := iterate_approximation_of_uniform_control P.g P.controlSet
    R.buffer (returnTime (j + 1))
    (fun _ hk => P.uniformControl_iterate (R.buffer_tube_inner S.b_pos) hk) ε hε
  exact ⟨δ, hδ, fun F hclose => (Hδ F hclose).1⟩

theorem exists_dynamical_tolerance : ∃ δ : ℝ, 0 < δ ∧ ∀ F : ℂ → ℂ,
    (∀ z ∈ P.controlSet, dist (F z) (P.g z) < δ) → RayOrbitProperty j S.a S.b F := by
  obtain ⟨δ₀, hδ₀, H₀⟩ := P.exists_barrier_tolerance
  obtain ⟨δ₁, hδ₁, H₁⟩ := P.exists_iterate_tolerance (by norm_num : (0 : ℝ) < 1 / 100)
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun F hclose => ?_⟩
  exact P.orbitProperty_of_close_iterates
    (H₀ F (fun z hz => (hclose z hz).trans_le (min_le_left _ _)))
    (H₁ F (fun z hz => (hclose z hz).trans_le (min_le_right _ _)))

theorem exists_extensions_tolerance : ∃ δ : ℝ, 0 < δ ∧ ∀ F : ℂ → ℂ,
    Differentiable ℂ F → (∀ z ∈ P.controlSet, dist (F z) (P.g z) < δ) →
    ∀ k ≤ returnTime (j + 1), HasQuantitativeExtensionOn (F^[k]) R.nextRegion := by
  classical
  have hU := R.buffer_tube_inner S.b_pos
  obtain ⟨r, hr, htube⟩ := R.nextRegion_tube_buffer S.b_pos
  have hcert (i : Fin (returnTime (j + 1) + 1)) :
      ∃ δ : ℝ, 0 < δ ∧ ∀ F : ℂ → ℂ, Differentiable ℂ F →
        (∀ z ∈ P.controlSet, dist (F z) (P.g z) < δ) →
        HasQuantitativeExtensionOn (F^[i.val]) R.nextRegion := by
    have hi := Nat.le_of_lt_succ i.isLt
    obtain ⟨H, he, L, L', hL, hL'⟩ := P.iterate_extensions hi
    obtain ⟨δ, hδ, Hδ⟩ := approximate_bilipschitz_iterate P.g P.controlSet R.buffer R.nextRegion
      (isOpen_openHalfStrip _ _ _) i
      (fun k hk => P.uniformControl_iterate hU (hk.trans_le hi))
      ((P.iterate_holomorphic hi).mono hU.subset) H (he.mono hU.subset) hL hL'
      hr htube (by norm_num : (0 : ℝ) < 1)
    exact ⟨δ, hδ, fun F hF hclose => (Hδ F hF hclose).1⟩
  choose d hd H using hcert
  obtain ⟨δ, hδ, hδd⟩ := exists_common_positive_bound d hd
  refine ⟨δ, hδ, fun F hF hclose k hk => ?_⟩
  exact H ⟨k, Nat.lt_succ_of_le hk⟩ F hF
    (fun z hz => (hclose z hz).trans_le (hδd _))

theorem exists_orbit_tube_tolerance : ∃ δ : ℝ, 0 < δ ∧ ∀ F : ℂ → ℂ,
    (∀ z ∈ P.controlSet, dist (F z) (P.g z) < δ) →
    ∀ k < returnTime (j + 1), HasUniformTube ((F^[k]) '' R.nextRegion) (background (j + 1)) := by
  classical
  have hcert (i : Fin (returnTime (j + 1))) := P.orbit_tubes i.isLt
  choose r hr htube using hcert
  obtain ⟨s, hs, hsr⟩ := exists_common_positive_bound r hr
  obtain ⟨δ, hδ, Hδ⟩ := P.exists_iterate_tolerance (half_pos hs)
  refine ⟨δ, hδ, fun F hclose k hk => ⟨s / 2, half_pos hs, ?_⟩⟩
  rintro _ ⟨z, hz, rfl⟩ w hw
  have hzU := (R.nextRegion_tube_buffer S.b_pos).subset hz
  have hzC := (R.buffer_tube_inner S.b_pos).subset hzU
  apply htube ⟨k, hk⟩ _ (mem_image_of_mem _ hzC)
  have he := Hδ F hclose k hk.le z hzU
  exact (dist_triangle w ((F^[k]) z) ((P.g^[k]) z)).trans_lt
    (by have hb := hsr ⟨k, hk⟩; change dist w ((F^[k]) z) < s / 2 at hw; linarith)

theorem exists_target_margin_tolerance : ∃ δ : ℝ, 0 < δ ∧ ∀ F : ℂ → ℂ,
    (∀ z ∈ P.controlSet, dist (F z) (P.g z) < δ) →
    ∀ z ∈ R.nextRegion,
      (height (j + 1) + 7) / 4 + 1 / 8 ≤ ((F^[returnTime (j + 1)]) z).im ∧
      ((F^[returnTime (j + 1)]) z).im ≤ (height (j + 1) + 11) / 4 - 1 / 8 := by
  obtain ⟨δ, hδ, Hδ⟩ := P.exists_iterate_tolerance (by norm_num : (0 : ℝ) < 1 / 8)
  refine ⟨δ, hδ, fun F hclose z hz => ?_⟩
  have hzU := (R.nextRegion_tube_buffer S.b_pos).subset hz
  have hzC := (R.buffer_tube_inner S.b_pos).subset hzU
  have he := Hδ F hclose (returnTime (j + 1)) le_rfl z hzU
  have heq : (P.g^[returnTime (j + 1)]) z = (S.f^[j + 1]) (R.ψ z) := by
    have h := P.iterate_eq_return (k := j + 1) le_rfl hzC
    convert h using 1 <;> congr 1 <;> simp only [returnTime_succ] <;> omega
  rw [heq, dist_eq_norm] at he
  have hi := abs_lt.mp ((Complex.abs_im_le_norm _).trans_lt he)
  simp only [Complex.sub_im] at hi
  have ht := R.target z (R.inner_subset_domain S.b_small hzC)
  constructor <;> linarith [ht.1, ht.2, hi.1, hi.2]

end RayReference

end EremenkosConjecture
