import EremenkosConjecture.ContinuumApproximationCharts
import EremenkosConjecture.ContinuumBarrierStability
import EremenkosConjecture.ContinuumOrbitProperty

open Set Metric Function

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

variable {X : Set ℂ} {D : ContinuumNeighbourhoods X rayBase (1 / 16)} {j : ℕ}
  {S : ContinuumStage D j} {R : ContinuumReturnChannel D S.f j (S.depth + 3)}

theorem ContinuumReference.exists_dynamical_tolerance (P : ContinuumReference S R)
    (hζ : rayBase ∈ X) : ∃ δ : ℝ, 0 < δ ∧ ∀ F : ℂ → ℂ,
      (∀ z ∈ P.controlSet, dist (F z) (P.reference.g z) < δ) →
      ContinuumOrbitProperty D j S.depth F := by
  obtain ⟨δ₀, hδ₀, h₀⟩ := P.exists_barrier_tolerance hζ
  obtain ⟨δ₁, hδ₁, h₁⟩ := P.exists_iterate_tolerance hζ (by norm_num : (0 : ℝ) < 1 / 100)
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun F hclose => ?_⟩
  exact P.orbitProperty_of_close_iterates hζ
    (h₀ F (fun z hz => (hclose z hz).trans_le (min_le_left _ _)))
    (h₁ F (fun z hz => (hclose z hz).trans_le (min_le_right _ _)))

theorem ContinuumReference.exists_charts_tolerance (P : ContinuumReference S R)
    (hζ : rayBase ∈ X) : ∃ δ : ℝ, 0 < δ ∧ ∀ F : ℂ → ℂ,
      Differentiable ℂ F → (∀ z ∈ P.controlSet, dist (F z) (P.reference.g z) < δ) →
      ∀ k ≤ returnTime (j + 1), Nonempty (LocalIterateChart F k (D.region (R.depth + 5))) := by
  classical
  have hcert (i : Fin (returnTime (j + 1) + 1)) :=
    P.exists_chart_tolerance hζ (Nat.le_of_lt_succ i.isLt)
  choose d hd h using hcert
  obtain ⟨δ, hδ, hδd⟩ := exists_common_positive_bound d hd
  refine ⟨δ, hδ, fun F hF hclose k hk => ?_⟩
  exact h ⟨k, Nat.lt_succ_of_le hk⟩ F hF
    (fun z hz => (hclose z hz).trans_le (hδd _))

theorem ContinuumReference.exists_orbit_tube_tolerance (P : ContinuumReference S R)
    (hζ : rayBase ∈ X) : ∃ δ : ℝ, 0 < δ ∧ ∀ F : ℂ → ℂ,
      (∀ z ∈ P.controlSet, dist (F z) (P.reference.g z) < δ) →
      ∀ k < returnTime (j + 1),
        HasUniformTube ((F^[k]) '' D.region (R.depth + 5)) (background (j + 1)) := by
  classical
  have hcert (i : Fin (returnTime (j + 1))) := P.orbit_tubes i.isLt
  choose r hr htube using hcert
  obtain ⟨s, hs, hsr⟩ := exists_common_positive_bound r hr
  obtain ⟨δ, hδ, happrox⟩ := P.exists_iterate_tolerance hζ (half_pos hs)
  refine ⟨δ, hδ, fun F hclose k hk => ⟨s / 2, half_pos hs, ?_⟩⟩
  rintro _ ⟨z, hz, rfl⟩ w hw
  have hzU := D.region_subset_openRegion hζ (i := R.depth + 2) (n := R.depth + 5) (by omega) hz
  have hzC := D.region_antitone (show R.depth ≤ R.depth + 5 by omega) hz
  apply htube ⟨k, hk⟩ _ (mem_image_of_mem _ hzC)
  have he := happrox F hclose k hk.le z hzU
  exact (dist_triangle w ((F^[k]) z) ((P.reference.g^[k]) z)).trans_lt
    (by have hb := hsr ⟨k, hk⟩; change dist w ((F^[k]) z) < s / 2 at hw; linarith)

theorem ContinuumReference.exists_target_margin_tolerance (P : ContinuumReference S R)
    (hζ : rayBase ∈ X) : ∃ δ : ℝ, 0 < δ ∧ ∀ F : ℂ → ℂ,
      (∀ z ∈ P.controlSet, dist (F z) (P.reference.g z) < δ) →
      ∀ z ∈ D.region (R.depth + 5),
        (height (j + 1) + 7) / 4 + 1 / 8 ≤ ((F^[returnTime (j + 1)]) z).im ∧
        ((F^[returnTime (j + 1)]) z).im ≤ (height (j + 1) + 11) / 4 - 1 / 8 := by
  obtain ⟨δ, hδ, happrox⟩ := P.exists_iterate_tolerance hζ (by norm_num : (0 : ℝ) < 1 / 8)
  refine ⟨δ, hδ, fun F hclose z hz => ?_⟩
  have hzU := D.region_subset_openRegion hζ (i := R.depth + 2) (n := R.depth + 5) (by omega) hz
  have hzC := D.region_antitone (show R.depth ≤ R.depth + 5 by omega) hz
  have he := happrox F hclose (returnTime (j + 1)) le_rfl z hzU
  rw [dist_eq_norm] at he
  have hi := abs_lt.mp ((Complex.abs_im_le_norm _).trans_lt he)
  simp only [Complex.sub_im] at hi
  have ht := P.target_margin z hzC
  constructor <;> linarith [ht.1, ht.2, hi.1, hi.2]

end EremenkosConjecture
