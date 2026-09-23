import FunctionTheory.Conformal.ThinAttachment
import FunctionTheory.Conformal.RadialKernelControl

open Set Metric Filter Complex
open scoped Topology

namespace FunctionTheory

/-- A shrinking gate and ordinary interior kernel convergence force uniform
leftward escape of the whole attached side. Only the limiting map has an
endpoint limit; no boundary convergence of the family is assumed. -/
theorem uniform_left_escape_of_shrinking_attachment
    {U : ℕ → Set ℂ} {V : Set ℂ} {F G : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    {ζ z₀ : ℂ} {R₀ : ℝ}
    (hU : ∀ n, IsOpen (U n)) (hF : ∀ n, DifferentiableOn ℂ (F n) (U n))
    (hinj : ∀ n, InjOn (F n) (U n)) (hmaps : ∀ n, MapsTo (F n) (U n) (ball 0 1))
    (hG : ∀ n, ContinuousOn (G n) (ball 0 1)) (hGU : ∀ n, MapsTo (G n) (ball 0 1) (U n))
    (hFG : ∀ n, RightInvOn (G n) (F n) (ball 0 1))
    (hGF : ∀ n, LeftInvOn (G n) (F n) (U n)) (hbase : ∀ n, G n 0 = z₀)
    (hR₀ : 0 < R₀) (hz₀ : ζ.re < z₀.re) (hfar : R₀ ≤ dist z₀ ζ)
    (harc : ∀ n, ∀ ρ ∈ Ioo 0 R₀,
      ∀ θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2), circleMap ζ ρ θ ∈ U n)
    (hgate : ∀ r > 0, ∀ᶠ n in atTop, ∀ w ∈ U n, w.re = ζ.re → dist w ζ ≤ r)
    (hconv : TendstoLocallyUniformlyOn F f atTop V)
    (hrad : ∀ t ∈ Ioo 0 R₀, ζ + (t : ℂ) ∈ V)
    (hend : Tendsto (fun t : ℝ => f (ζ + (t : ℂ))) (𝓝[>] 0) (𝓝 (-1))) :
    ∀ M : ℝ, ∀ᶠ n in atTop, ∀ x ∈ U n, x.re < ζ.re →
      (discToHorizontalStrip (F n x)).re < M := by
  intro M
  let δ := min (1 / 2 : ℝ) (Real.exp (M - 1))
  have hδ : 0 < δ := lt_min (by norm_num) (Real.exp_pos _)
  have hδ1 : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hlog : Real.log δ < M := by
    have h := Real.log_le_log hδ (min_le_right (1 / 2 : ℝ) (Real.exp (M - 1)))
    rw [Real.log_exp] at h
    linarith
  obtain ⟨R, hR, hanchor⟩ := exists_outer_radius_for_radial_kernel_control
    hconv hR₀ (half_pos hδ) hrad hend
  obtain ⟨r, hr, hbound⟩ := exists_gate_size_for_uniform_leftward_bound hδ hδ1 hR.1
  filter_upwards [hgate r hr.1, hanchor r hr.1] with n hn hclose
  have hb : (0 : ℂ) ∈ ball (0 : ℂ) 1 \ closedBall (-1 : ℂ) δ := by
    constructor
    · simp
    · simpa using (not_le.mpr hδ1)
  have h := hbound (U n) (F n) (G n) ζ 0 (hU n) (hF n) (hinj n) (hmaps n)
    (hG n) (hGU n) (hFG n) (hGF n) hn
    (fun ρ hρ => harc n ρ ⟨hr.1.trans hρ.1, hρ.2.trans hR.2⟩)
    (fun ρ hρ => hclose ρ ⟨hρ.1.le, hρ.2.le⟩) hb
    (by simpa only [hbase n] using hz₀)
    (by simpa only [hbase n] using hR.2.le.trans hfar)
  exact fun x hx hleft => (h x hx hleft).trans_lt hlog

/-- Positive scaling and translation to the horizontal target strip preserve
uniform leftward escape. -/
theorem uniform_left_escape_affine
    {F : ℕ → ℂ → ℂ} {X : Set ℂ} {c : ℝ} {b : ℂ} (hc : 0 < c)
    (hleft : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ x ∈ X, (F n x).re < M) :
    ∀ M : ℝ, ∀ᶠ n in atTop, ∀ x ∈ X, ((c : ℂ) * F n x + b).re < M := by
  intro M
  filter_upwards [hleft ((M - b.re) / c)] with n hn
  intro x hx
  have h := (lt_div_iff₀ hc).mp (hn x hx)
  simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  nlinarith

end FunctionTheory
