import EremenkosConjecture.ContinuumApproximationStability

open Set Metric Function

namespace EremenkosConjecture

open Scaffolding

structure ContinuumStep {X : Set ℂ} {D : ContinuumNeighbourhoods X rayBase (1 / 16)}
    {j : ℕ} (S : ContinuumStage D j) (T : ContinuumStage D (j + 1)) : Prop where
  reserve : T.reserve ≤ S.reserve / 2
  depth : S.depth < T.depth
  correction : ∀ z ∈ background j, dist (T.f z) (S.f z) ≤ S.reserve / 4
  stable : ∀ F : ℂ → ℂ,
    (∀ z ∈ background (j + 1), dist (F z) (T.f z) < T.reserve) →
    ContinuumOrbitProperty D j S.depth F

theorem exists_next_continuumStage {X : Set ℂ}
    {D : ContinuumNeighbourhoods X rayBase (1 / 16)}
    (hX : IsCompact X) (hconn : IsConnected X) (hfull : IsConnected Xᶜ)
    (hζ : rayBase ∈ X) (hmax : ∀ z ∈ X, z.re ≤ rayBase.re)
    (hball : X ⊆ ball rayBase (1 / 16)) {j : ℕ} (S : ContinuumStage D j) :
    ∃ T : ContinuumStage D (j + 1), ContinuumStep S T := by
  obtain ⟨R⟩ := exists_continuumReturnChannel D hX hconn hfull hζ hmax hball
    S.entire.differentiableOn S.affine_le j (S.depth + 3)
  obtain ⟨P⟩ := exists_continuumReference hζ S R
  obtain ⟨d₀, hd₀, h₀⟩ := P.exists_dynamical_tolerance hζ
  obtain ⟨d₁, hd₁, h₁⟩ := P.exists_charts_tolerance hζ
  obtain ⟨d₂, hd₂, h₂⟩ := P.exists_orbit_tube_tolerance hζ
  obtain ⟨d₃, hd₃, h₃⟩ := P.exists_target_margin_tolerance hζ
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
  obtain ⟨F, hF, hclose⟩ := P.exists_entire_approximation hζ hε
  have hclosed : ∀ z ∈ P.controlSet, dist (F z) (P.reference.g z) < d :=
    fun z hz => (hclose z hz).trans (by linarith)
  have hclosed' (e : ℝ) (he : d ≤ e) : ∀ z ∈ P.controlSet, dist (F z) (P.reference.g z) < e :=
    fun z hz => (hclosed z hz).trans_le he
  let r := min (S.reserve / 2) (d / 4)
  have hr : 0 < r := lt_min (div_pos S.reserve_pos (by norm_num)) (by positivity)
  have hrr : r ≤ S.reserve / 2 := min_le_left _ _
  have hrd : r ≤ d / 4 := min_le_right _ _
  have hbg : ∀ z ∈ background j, dist (F z) (S.f z) < ε := by
    intro z hz
    simpa only [P.reference.background_eq hz] using hclose z (Or.inl (Or.inl hz))
  let T : ContinuumStage D (j + 1) := {
    f := F
    entire := hF
    depth := R.depth + 5
    reserve := r
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
    charts := h₁ F hF (hclosed' d₁ hd₁')
    orbitTubes := h₂ F (hclosed' d₂ hd₂')
    targetMargin := ⟨1 / 8, by norm_num, h₃ F (hclosed' d₃ hd₃')⟩ }
  refine ⟨T, ⟨hrr, ?_, ?_, ?_⟩⟩
  · change S.depth < R.depth + 5
    have := R.later
    omega
  · intro z hz
    exact (hbg z hz).le.trans hεr
  · intro G hG
    apply h₀ G
    intro z hz
    have hG' := hG z (P.controlSet_subset_background hz)
    change dist (G z) (F z) < r at hG'
    have hF' := hclose z hz
    exact (dist_triangle (G z) (F z) (P.reference.g z)).trans_lt (by linarith)

end EremenkosConjecture
