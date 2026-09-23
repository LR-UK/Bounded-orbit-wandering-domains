import FunctionTheory.Conformal.SchottkyEstimate

open Set Metric
namespace FunctionTheory
set_option autoImplicit false

/-- The corresponding majorant for omission of zero and one. -/
noncomputable def schottkyZeroOneMajorant (R t : ℝ) : ℝ :=
  (schottkyMajorant (2*R+1) t+1)/2

/-- Schottky's estimate with the usual omitted values zero and one. -/
theorem norm_le_schottkyZeroOneMajorant {f : ℂ → ℂ} {R t : ℝ}
    (ht : 0≤t) (ht1 : t<1)
    (hf : AnalyticOnNhd ℂ f (ball (0:ℂ) 1))
    (hzero : ∀ z∈ball (0:ℂ) 1, f z≠0)
    (hone : ∀ z∈ball (0:ℂ) 1, f z≠1)
    (hbase : ‖f 0‖≤R) {z : ℂ} (hz : ‖z‖≤t) :
    ‖f z‖≤schottkyZeroOneMajorant R t := by
  let F := fun w => (2:ℂ)*f w-1
  have hF : AnalyticOnNhd ℂ F (ball (0:ℂ) 1) := (analyticOnNhd_const.mul hf).sub analyticOnNhd_const
  have hp : ∀ w∈ball (0:ℂ) 1, F w≠1 := by
    intro w hw H
    exact hone w hw (by dsimp [F] at H; linear_combination H/2)
  have hm : ∀ w∈ball (0:ℂ) 1, F w≠-1 := by
    intro w hw H
    exact hzero w hw (by dsimp [F] at H; linear_combination H/2)
  have hb : ‖F 0‖≤2*R+1 := by
    calc
      ‖F 0‖ ≤ ‖(2:ℂ)*f 0‖+‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2*‖f 0‖+1 := by rw [norm_mul]; norm_num
      _ ≤ 2*R+1 := by linarith
  have H := norm_le_schottkyMajorant ht ht1 hF hp hm hb hz
  have H' : 2*‖f z‖≤‖F z‖+1 := by
    calc
      2*‖f z‖ = ‖(2:ℂ)*f z‖ := by rw [norm_mul]; norm_num
      _ = ‖F z+1‖ := by congr 1; dsimp [F]; ring
      _ ≤ ‖F z‖+1 := by simpa only [norm_one] using norm_add_le (F z) 1
  unfold schottkyZeroOneMajorant
  linarith

/-- Schottky's estimate on an arbitrary disc, with its radius kept explicit. -/
theorem norm_le_schottkyZeroOneMajorant_on_disc {f : ℂ → ℂ} {c : ℂ} {r R t : ℝ}
    (hr : 0<r) (ht : 0≤t) (ht1 : t<1)
    (hf : AnalyticOnNhd ℂ f (ball c r))
    (hzero : ∀ z∈ball c r, f z≠0) (hone : ∀ z∈ball c r, f z≠1)
    (hbase : ‖f c‖≤R) {z : ℂ} (hz : ‖z-c‖≤t*r) :
    ‖f z‖≤schottkyZeroOneMajorant R t := by
  let F := fun w : ℂ => f (c+(r:ℂ)*w)
  have hinside : ∀ w∈ball (0:ℂ) 1, c+(r:ℂ)*w∈ball c r := by
    intro w hw
    rw [mem_ball_iff_norm,add_sub_cancel_left,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hr]
    simpa only [mul_one] using mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hw) hr
  have hF : AnalyticOnNhd ℂ F (ball (0:ℂ) 1) := by
    intro w hw
    exact (hf _ (hinside w hw)).comp (f := fun w : ℂ => c+(r:ℂ)*w) (x := w)
      (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
  have hbaseF : ‖F 0‖≤R := by simpa only [F,mul_zero,add_zero] using hbase
  let w : ℂ := (z-c)/(r:ℂ)
  have hw : ‖w‖≤t := by
    dsimp [w]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    exact (div_le_iff₀ hr).mpr hz
  have H := norm_le_schottkyZeroOneMajorant ht ht1 hF
    (fun w hw => hzero _ (hinside w hw)) (fun w hw => hone _ (hinside w hw)) hbaseF hw
  have hrC : (r:ℂ)≠0 := by exact_mod_cast hr.ne'
  have heq : F w=f z := by
    dsimp [F,w]
    congr 1
    field_simp
    ring
  rwa [heq] at H

end FunctionTheory
