import PunctureDensityLimits

open Set Metric Function Filter
open scoped Topology

namespace AreaDeficit

/-- Omission of two fixed values and a fixed central value gives a
uniform bound on every strictly smaller source disc. -/
theorem omitted_pair_bounded_subdisc {p : ℕ → ℂ → ℂ} {a b z : ℂ}
    (hab : a ≠ b) (hp : ∀ n, DifferentiableOn ℂ (p n) (ball 0 1))
    (ha : ∀ n w, w ∈ ball (0 : ℂ) 1 → p n w ≠ a)
    (hb : ∀ n w, w ∈ ball (0 : ℂ) 1 → p n w ≠ b)
    (h0 : ∀ n, p n 0 = z) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ∃ M : ℝ, ∀ n w, w ∈ ball (0 : ℂ) r → ‖p n w‖ ≤ M := by
  let q : ℕ → ℂ → ℂ := fun n w => (p n w - a) / (b - a)
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hq : ∀ n, AnalyticOnNhd ℂ (q n) (ball 0 1) :=
    fun n => (((hp n).analyticOnNhd isOpen_ball).sub analyticOnNhd_const).div_const
  have hq0 : ∀ n w, w ∈ ball (0 : ℂ) 1 → q n w ≠ 0 :=
    fun n w hw => div_ne_zero (sub_ne_zero.mpr (ha n w hw)) hba
  have hq1 : ∀ n w, w ∈ ball (0 : ℂ) 1 → q n w ≠ 1 := by
    intro n w hw he
    have hh := (div_eq_one_iff_eq hba).mp he
    exact hb n w hw (sub_left_injective hh)
  let M := FunctionTheory.schottkyZeroOneMajorant ‖(z - a) / (b - a)‖ r
  refine ⟨‖b - a‖ * M + ‖a‖, ?_⟩
  intro n w hw
  have hbound : ‖q n w‖ ≤ M :=
    FunctionTheory.norm_le_schottkyZeroOneMajorant hr hr1 (hq n) (hq0 n) (hq1 n)
      (by simp [q, h0 n]) (mem_ball_zero_iff.mp hw).le
  have he : p n w = (b - a) * q n w + a := by dsimp [q]; field_simp; ring
  rw [he]
  exact (norm_add_le _ _).trans (by rw [norm_mul]; gcongr)

end AreaDeficit
