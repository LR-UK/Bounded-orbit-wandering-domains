import EremenkosConjecture.RayApproximationStability

/-! # Existence of a successor stage in the ray construction -/

open Set Metric Function

namespace EremenkosConjecture

open Scaffolding

structure RayStep {j : ℕ} (S : RayStage j) (T : RayStage (j + 1)) : Prop where
  reserve : T.reserve ≤ S.reserve / 2
  width : T.a ≤ S.a / 2
  height : T.b ≤ S.b / 2
  correction : ∀ z ∈ background j, dist (T.f z) (S.f z) ≤ S.reserve / 4
  stable : ∀ F : ℂ → ℂ,
    (∀ z ∈ background (j + 1), dist (F z) (T.f z) < T.reserve) →
    RayOrbitProperty j S.a S.b F

theorem exists_next_rayStage {j : ℕ} (S : RayStage j) :
    ∃ T : RayStage (j + 1), RayStep S T := by
  obtain ⟨R⟩ := exists_rayReturnChannel S.entire.differentiableOn S.affine_le j S.a_pos S.b_pos S.b_small
  obtain ⟨P⟩ := exists_rayReference S R
  obtain ⟨d₀, hd₀, H₀⟩ := P.exists_dynamical_tolerance
  obtain ⟨d₁, hd₁, H₁⟩ := P.exists_extensions_tolerance
  obtain ⟨d₂, hd₂, H₂⟩ := P.exists_orbit_tube_tolerance
  obtain ⟨d₃, hd₃, H₃⟩ := P.exists_target_margin_tolerance
  let d := min (min d₀ d₁) (min d₂ d₃)
  have hd : 0 < d := lt_min (lt_min hd₀ hd₁) (lt_min hd₂ hd₃)
  have hd₀' : d ≤ d₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hd₁' : d ≤ d₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hd₂' : d ≤ d₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hd₃' : d ≤ d₃ := (min_le_right _ _).trans (min_le_right _ _)
  let ε := min (S.reserve / 4) (d / 4)
  have hε : 0 < ε := lt_min (div_pos S.reserve_pos (by norm_num)) (by positivity)
  have hεr : ε ≤ S.reserve / 4 := min_le_left _ _
  have hεd : ε ≤ d / 4 := min_le_right _ _
  obtain ⟨F, hF, hclose⟩ := P.exists_entire_approximation hε
  have hclosed : ∀ z ∈ P.controlSet, dist (F z) (P.g z) < d :=
    fun z hz => (hclose z hz).trans (by linarith)
  have hclosed' (e : ℝ) (he : d ≤ e) : ∀ z ∈ P.controlSet, dist (F z) (P.g z) < e :=
    fun z hz => (hclosed z hz).trans_le he
  let r := min (S.reserve / 2) (d / 4)
  have hr : 0 < r := lt_min (div_pos S.reserve_pos (by norm_num)) (by positivity)
  have hrr : r ≤ S.reserve / 2 := min_le_left _ _
  have hrd : r ≤ d / 4 := min_le_right _ _
  have hbg : ∀ z ∈ background j, dist (F z) (S.f z) < ε := by
    intro z hz
    simpa only [P.background_eq hz] using hclose z (Or.inl (Or.inl hz))
  have hreg : closedHalfStrip rayBase (2 * (R.η / 64)) (2 * (S.b / 64)) = R.nextRegion := by
    dsimp only [RayReturnChannel.nextRegion]
    congr 1 <;> ring
  let T : RayStage (j + 1) := {
    f := F
    entire := hF
    a := R.η / 64
    b := S.b / 64
    reserve := r
    a_pos := div_pos R.η_pos (by norm_num)
    b_pos := div_pos S.b_pos (by norm_num)
    a_small := by linarith [R.η_small, S.a_small]
    b_small := by linarith [S.b_small, S.b_pos]
    reserve_pos := hr
    affine := by
      intro z hz
      have he := hbg z (closedSourceStrips_subset_background j hz)
      rw [dist_eq_norm] at he
      have ht := dist_triangle (F z) (S.f z) (5 * z)
      simp only [dist_eq_norm] at ht
      have hs := S.affine z hz
      linarith
    trapping := by
      intro z hz
      have he := hbg z (trappingDisk_subset_background j hz)
      rw [dist_eq_norm] at he
      have ht := norm_le_norm_sub_add (F z) (S.f z)
      have hs := S.trapping z hz
      linarith
    extensions := by
      rw [hreg]
      exact H₁ F hF (hclosed' d₁ hd₁')
    orbitTubes := by
      rw [hreg]
      exact H₂ F (hclosed' d₂ hd₂')
    targetMargin := by
      rw [hreg]
      exact ⟨1 / 8, by norm_num, H₃ F (hclosed' d₃ hd₃')⟩ }
  refine ⟨T, ⟨hrr, ?_, ?_, ?_, ?_⟩⟩
  · change R.η / 64 ≤ S.a / 2
    linarith [R.η_small, S.a_pos]
  · change S.b / 64 ≤ S.b / 2
    linarith [S.b_pos]
  · intro z hz
    exact (hbg z hz).le.trans hεr
  · intro G hG
    apply H₀ G
    intro z hz
    have hG' := hG z (P.controlSet_subset_background hz)
    change dist (G z) (F z) < r at hG'
    have hF' := hclose z hz
    exact (dist_triangle (G z) (F z) (P.g z)).trans_lt (by linarith)

end EremenkosConjecture
