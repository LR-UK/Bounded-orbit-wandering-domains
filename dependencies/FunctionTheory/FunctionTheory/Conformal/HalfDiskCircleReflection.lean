import FunctionTheory.Conformal.ReflectionInjectivity
import FunctionTheory.Conformal.CayleyCoordinates

open Set Metric Complex Filter
open scoped Topology ComplexConjugate

namespace FunctionTheory

/-- Reflect a locally univalent half-disk map whose diameter maps into the
unit circle. Rotation and a Cayley coordinate put both boundaries on the
imaginary axis. Only local continuity is required. -/
theorem exists_reflection_of_half_disk_map_to_circle
    {H : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hHc : ContinuousOn H (ball 0 r ∩ {z : ℂ | 0 ≤ z.re}))
    (hHd : DifferentiableOn ℂ H (ball 0 r ∩ {z : ℂ | 0 < z.re}))
    (hHi : InjOn H (ball 0 r ∩ {z : ℂ | 0 < z.re}))
    (hHD : MapsTo H (ball 0 r ∩ {z : ℂ | 0 < z.re}) (ball 0 1))
    (hHa : ∀ z ∈ ball (0 : ℂ) r, z.re = 0 → H z ∈ sphere (0 : ℂ) 1) :
    ∃ (δ : ℝ) (F : ℂ → ℂ), 0 < δ ∧ δ ≤ r ∧
      DifferentiableOn ℂ F (ball 0 δ) ∧ InjOn F (ball 0 δ) ∧ F 0 = 0 ∧
      EqOn F (fun z => cayleyCoordinate (H z / H 0))
        (ball 0 δ ∩ {z : ℂ | 0 ≤ z.re}) ∧
      (∀ z ∈ ball 0 δ, F (-conj z) = -conj (F z)) ∧
      ∀ z ∈ ball (0 : ℂ) δ, 0 < z.re → 0 < (F z).re := by
  have hξ : ‖H 0‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using hHa 0 (mem_ball_self hr) rfl
  have hξ0 : H 0 ≠ 0 := norm_ne_zero_iff.mp (by rw [hξ]; norm_num)
  let g : ℂ → ℂ := fun z => H z / H 0
  have hg0 : g 0 = 1 := div_self hξ0
  have hgc : ContinuousOn g (ball 0 r ∩ {z : ℂ | 0 ≤ z.re}) := hHc.div_const _
  obtain ⟨ε, hε, hsmall⟩ := Metric.continuousWithinAt_iff.mp
    (hgc 0 ⟨mem_ball_self hr, by simp⟩) 1 zero_lt_one
  let δ := min ε r
  have hδ : 0 < δ := lt_min hε hr
  have hδr : δ ≤ r := min_le_right _ _
  have hden : ∀ z ∈ ball (0 : ℂ) δ ∩ {z : ℂ | 0 ≤ z.re}, 1 + g z ≠ 0 := by
    intro z hz he
    have hnear := hsmall ⟨ball_subset_ball hδr hz.1, hz.2⟩
      (lt_of_lt_of_le (mem_ball.mp hz.1) (min_le_left _ _))
    have hgz : g z = -1 := by linear_combination he
    norm_num [hg0, hgz, dist_eq_norm] at hnear
  let Q : ℂ → ℂ := fun z => cayleyCoordinate (g z)
  have hQc : ContinuousOn Q (ball 0 δ ∩ {z : ℂ | 0 ≤ z.re}) := by
    intro z hz
    exact (differentiableAt_cayleyCoordinate (hden z hz)).continuousAt.comp_continuousWithinAt
      ((hgc.mono (inter_subset_inter_left _ (ball_subset_ball hδr))) z hz)
  have hQd : DifferentiableOn ℂ Q (ball 0 δ ∩ {z : ℂ | 0 < z.re}) := by
    intro z hz
    exact (differentiableAt_cayleyCoordinate (hden z ⟨hz.1, (show 0 < z.re from hz.2).le⟩)).comp_differentiableWithinAt z
      ((hHd.div_const _).mono (inter_subset_inter_left _ (ball_subset_ball hδr)) z hz)
  have hQ0 : Q 0 = 0 := by simp [Q, hg0]
  have hQa : ∀ z ∈ ball (0 : ℂ) δ, z.re = 0 → (Q z).re = 0 := by
    intro z hz hz0
    have hn : ‖H z‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using hHa z (ball_subset_ball hδr hz) hz0
    have hgn : ‖g z‖ = 1 := by simp only [g, norm_div, hn, hξ, div_self one_ne_zero]
    simp only [Q, re_cayleyCoordinate, normSq_eq_norm_sq, hgn, one_pow, sub_self, zero_div]
  have hQpos : ∀ z ∈ ball (0 : ℂ) δ, 0 < z.re → 0 < (Q z).re := by
    intro z hz hzre
    apply re_cayleyCoordinate_pos_of_mem_ball
    have hnorm := hHD ⟨ball_subset_ball hδr hz, hzre⟩
    simpa only [g, mem_ball, dist_zero_right, norm_div, hξ, div_one] using hnorm
  have hQi : InjOn Q (ball 0 δ ∩ {z : ℂ | 0 < z.re}) := by
    intro z hz w hw heq
    have heqg := cayleyCoordinate_injOn (hden z ⟨hz.1, (show 0 < z.re from hz.2).le⟩)
      (hden w ⟨hw.1, (show 0 < w.re from hw.2).le⟩) heq
    apply hHi ⟨ball_subset_ball hδr hz.1, hz.2⟩ ⟨ball_subset_ball hδr hw.1, hw.2⟩
    exact (div_left_inj' hξ0).mp heqg
  have hsym : MapsTo (fun z : ℂ => -conj z) (ball 0 δ) (ball 0 δ) :=
    fun z hz => by simpa only [mem_ball, dist_zero_right, norm_neg, norm_conj] using hz
  obtain ⟨F, hFd, hFQ, hFs⟩ := exists_holomorphic_reflection_across_imaginary_axis
    isOpen_ball hsym hQc hQd hQa
  have hF0 : F 0 = 0 := (hFQ ⟨mem_ball_self hδ, by simp⟩).trans hQ0
  have hFpos : ∀ z ∈ ball (0 : ℂ) δ, 0 < z.re → 0 < (F z).re := by
    intro z hz hzre
    rw [hFQ ⟨hz, hzre.le⟩]
    exact hQpos z hz hzre
  have hFi : InjOn F (ball 0 δ) :=
    injOn_of_imaginary_reflection isOpen_ball (convex_ball (0 : ℂ) δ).isPreconnected
      (mem_ball_self hδ) hsym hFd hFs hF0 hFpos (by
        intro z hz w hw heq
        apply hQi hz hw
        rwa [hFQ ⟨hz.1, (show 0 < z.re from hz.2).le⟩,
          hFQ ⟨hw.1, (show 0 < w.re from hw.2).le⟩] at heq)
  exact ⟨δ, F, hδ, hδr, hFd, hFi, hF0, hFQ, hFs, hFpos⟩

end FunctionTheory
