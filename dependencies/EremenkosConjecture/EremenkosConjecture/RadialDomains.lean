import EremenkosConjecture.PlaneTopology
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.LocallyPathConnected

open Set Metric Function

namespace EremenkosConjecture

theorem exists_inner_radius {K : Set ℂ} (hK : IsCompact K) {R : ℝ} (hR : 0 < R)
    (hKR : K ⊆ ball 0 R) : ∃ r : ℝ, 0 < r ∧ r < R ∧ K ⊆ ball 0 r := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨R / 2, by positivity, by linarith, empty_subset _⟩
  · obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
    have hzR : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hKR hz
    refine ⟨(‖z‖ + R) / 2, by positivity, by linarith, ?_⟩
    intro w hw
    rw [mem_ball, dist_zero_right]
    have hwz : ‖w‖ ≤ ‖z‖ := hmax hw
    linarith

noncomputable def radialRetraction (r : ℝ) (z : ℂ) : ℂ := (r / max r ‖z‖) • z

theorem continuous_radialRetraction {r : ℝ} (hr : 0 < r) : Continuous (radialRetraction r) := by
  unfold radialRetraction
  have hc : Continuous (fun z : ℂ => r / max r ‖z‖) :=
    continuous_const.div (continuous_const.max continuous_norm)
      (fun z => ne_of_gt (lt_max_of_lt_left hr))
  exact hc.smul continuous_id

theorem radialRetraction_eq_self {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≤ r) :
    radialRetraction r z = z := by
  simp only [radialRetraction, max_eq_left hz, div_self (ne_of_gt hr), one_smul]

theorem norm_radialRetraction_of_le {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : r ≤ ‖z‖) :
    ‖radialRetraction r z‖ = r := by
  rw [radialRetraction, max_eq_right hz, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hr.le (norm_nonneg z)), div_mul_cancel₀ _ (ne_of_gt (hr.trans_le hz))]

theorem norm_radialRetraction_le {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ‖radialRetraction r z‖ ≤ r := by
  rcases le_total ‖z‖ r with hz | hz
  · rwa [radialRetraction_eq_self hr hz]
  · exact (norm_radialRetraction_of_le hr hz).le

theorem radialRetraction_avoids {K : Set ℂ} {r : ℝ} (hr : 0 < r) (hKr : K ⊆ ball 0 r)
    {z : ℂ} (hz : z ∉ K) : radialRetraction r z ∉ K := by
  rcases le_total ‖z‖ r with hzr | hrz
  · rwa [radialRetraction_eq_self hr hzr]
  · intro H
    have H' := hKr H
    rw [mem_ball, dist_zero_right, norm_radialRetraction_of_le hr hrz] at H'
    exact (lt_irrefl r H')

/-- Removing a full compactum contained in a disk leaves a path-connected domain. -/
theorem isPathConnected_ball_sdiff_full {K : Set ℂ} (hK : IsCompact K)
    (hfull : IsConnected Kᶜ) {R : ℝ} (hR : 0 < R) (hKR : K ⊆ ball 0 R) :
    IsPathConnected (ball (0 : ℂ) R \ K) := by
  have hpc : IsPathConnected Kᶜ := hK.isClosed.isOpen_compl.isConnected_iff_isPathConnected.mp hfull
  obtain ⟨r, hr, hrR, hKr⟩ := exists_inner_radius hK hR hKR
  have hne : (ball (0 : ℂ) R \ K).Nonempty := by
    refine ⟨(r : ℂ), ?_, ?_⟩
    · simpa only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hrR
    · intro H
      have H' := hKr H
      simp only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
        lt_self_iff_false] at H'
  refine isPathConnected_iff.mpr ⟨hne, ?_⟩
  intro a ha b hb
  have hcab : IsCompact (insert a (insert b K)) := hK.insert b |>.insert a
  have habR : insert a (insert b K) ⊆ ball (0 : ℂ) R := by
    intro z hz
    rcases hz with rfl | rfl | hz
    · exact ha.1
    · exact hb.1
    · exact hKR hz
  obtain ⟨s, hs, hsR, hKs⟩ := exists_inner_radius hcab hR habR
  have ha' : ‖a‖ ≤ s := (mem_ball_zero_iff.mp (hKs (mem_insert a _))).le
  have hb' : ‖b‖ ≤ s := (mem_ball_zero_iff.mp (hKs (mem_insert_of_mem a (mem_insert b K)))).le
  have hKsmall : K ⊆ ball 0 s := fun z hz => hKs (mem_insert_of_mem a (mem_insert_of_mem b hz))
  have hjoin := (hpc.joinedIn a ha.2 b hb.2).map (continuous_radialRetraction hs).continuousOn
  rw [radialRetraction_eq_self hs ha', radialRetraction_eq_self hs hb'] at hjoin
  apply hjoin.mono
  rintro z ⟨w, hw, rfl⟩
  exact ⟨by simpa only [mem_ball, dist_zero_right] using (norm_radialRetraction_le hs w).trans_lt hsR,
    radialRetraction_avoids hs hKsmall hw⟩

end EremenkosConjecture
