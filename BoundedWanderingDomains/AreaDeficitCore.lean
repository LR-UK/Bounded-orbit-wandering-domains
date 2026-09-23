import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# The regularisation-to-area-bound implication

Scope: this file retains the original measure-theoretic positive-part argument
from explicit smooth-calculus inputs. The full analytic proof now appears in
the accompanying modules Regularisation, GreenIdentity, LaplacianChain,
LogBarrier, PunctureRegularisation, PositivePart, and DensityDeficit.
Their main theorems derive the analytic inputs, including finite punctures.
Poincare metric comparison and the dynamical application remain outside this
formalisation. The normalisation throughout is curvature -1.

In the intended application:
  u = log (rho / eta), h = rho^2 - eta^2,
  b n = beta_n(u), c n = beta_n'(u), d n = beta_n''(u),
  g = |grad u|^2, L = Delta chi.
The hypothesis `green` is the ordinary smooth chain rule followed by
integration by parts. The positive-part Laplacian inequality and the
final area bound are conclusions, not hypotheses.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace AreaDeficitCore

variable {S : Type*} [MeasurableSpace S] {mu : Measure S}

/-- The first-derivative profile of the explicit one-sided cubic transition. -/
noncomputable def slope (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if 1 ≤ t then 1 else 3 * t ^ 2 - 2 * t ^ 3

/-- Its second-derivative profile. -/
noncomputable def bend (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if 1 ≤ t then 0 else 6 * t * (1 - t)

/-- The integrated transition; it is mathematically C², but that assertion
and its derivative identities are not claimed by this Lean file. -/
noncomputable def primitive (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if 1 ≤ t then t - 1 / 2 else t ^ 3 - t ^ 4 / 2

theorem slope_bounds (t : ℝ) : 0 ≤ slope t ∧ slope t ≤ 1 := by
  unfold slope
  split_ifs with h0 h1
  · norm_num
  · norm_num
  · have ht : 0 ≤ t := le_of_not_ge h0
    have ht1 : t ≤ 1 := le_of_not_ge h1
    constructor
    · nlinarith [mul_nonneg (sq_nonneg t) (show 0 ≤ 3 - 2 * t by linarith)]
    · nlinarith [mul_nonneg (sq_nonneg (1 - t)) (show 0 ≤ 1 + 2 * t by linarith)]

theorem bend_nonneg (t : ℝ) : 0 ≤ bend t := by
  unfold bend
  split_ifs with h0 h1
  · norm_num
  · norm_num
  · exact mul_nonneg (mul_nonneg (by norm_num) (le_of_not_ge h0))
      (sub_nonneg.mpr (le_of_not_ge h1))

theorem primitive_bounds (t : ℝ) : 0 ≤ primitive t ∧ primitive t ≤ max t 0 := by
  unfold primitive
  split_ifs with h0 h1
  · simp [max_eq_right h0]
  · rw [max_eq_left (by linarith : 0 ≤ t)]
    constructor <;> linarith
  · have ht : 0 ≤ t := le_of_not_ge h0
    have ht1 : t ≤ 1 := le_of_not_ge h1
    rw [max_eq_left ht]
    have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht 3
    have ht4 : 0 ≤ t ^ 4 := pow_nonneg ht 4
    have ht3le : t ^ 3 ≤ t := by
      nlinarith [mul_nonneg ht (sub_nonneg.mpr ht1),
        mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht1)]
    constructor
    · nlinarith [mul_nonneg ht3 (show 0 ≤ 1 - t / 2 by linarith)]
    · linarith

/-- The derivative profiles converge to the indicator of the positive half-line. -/
theorem slope_scaled_tendsto (u : ℝ) :
    Tendsto (fun n : ℕ => slope (((n : ℝ) + 1) * u)) atTop
      (𝓝 (if 0 < u then 1 else 0)) := by
  by_cases hu : 0 < u
  · have hdiv : ∃ N : ℕ, 1 / u < N := exists_nat_gt (1 / u)
    obtain ⟨N, hN⟩ := hdiv
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnr : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
    have hscale : 1 ≤ ((n : ℝ) + 1) * u := by
      have hnu : 1 < (N : ℝ) * u := (div_lt_iff₀ hu).mp hN
      nlinarith
    simp [hu, slope, show ¬ ((n : ℝ) + 1) * u ≤ 0 by linarith, hscale]
  · have hu0 : u ≤ 0 := le_of_not_gt hu
    have heq : (fun n : ℕ => slope (((n : ℝ) + 1) * u)) = fun _ => 0 := by
      funext n
      simp [slope, mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ (n : ℝ) + 1) hu0]
    simp [hu, heq]

/-- The curvature difference has the sign of the logarithmic density ratio. -/
theorem curvature_sign {u b : ℝ} (hb : 0 ≤ b) :
    (0 < u → 0 ≤ b * (Real.exp (2 * u) - 1)) ∧
    (u ≤ 0 → b * (Real.exp (2 * u) - 1) ≤ 0) := by
  constructor
  · intro hu
    exact mul_nonneg hb (sub_nonneg.mpr (Real.one_le_exp (by linarith)))
  · intro hu
    exact mul_nonpos_of_nonneg_of_nonpos hb
      (sub_nonpos.mpr (Real.exp_le_one_iff.mpr (by linarith)))

/-- A one-sided convex regularisation never retains the negative part. -/
theorem regularized_source_nonneg {u h c : ℝ}
    (hpos : 0 < u → 0 ≤ h) (hc : 0 ≤ c) (hzero : u ≤ 0 → c = 0) :
    0 ≤ c * h := by
  by_cases hu : 0 < u
  · exact mul_nonneg hc (hpos hu)
  · simp [hzero (le_of_not_gt hu)]

/-- Derivative convergence gives precisely the positive part of the source. -/
theorem regularized_source_tendsto {u h : ℝ} {c : ℕ → ℝ}
    (hpos : 0 < u → 0 ≤ h) (hneg : u ≤ 0 → h ≤ 0)
    (hc : Tendsto c atTop (𝓝 (if 0 < u then 1 else 0))) :
    Tendsto (fun n => c n * h) atTop (𝓝 (max h 0)) := by
  by_cases hu : 0 < u
  · simpa [hu, max_eq_left (hpos hu)] using hc.mul_const h
  · simpa [hu, max_eq_right (hneg (le_of_not_gt hu))] using hc.mul_const h

/-- The cutoff estimate for one smooth convex regularisation. -/
theorem smooth_cutoff_bound
    {b c d g h chi L : S → ℝ} {M : ℝ}
    (hchi : ∀ x, 0 ≤ chi x)
    (hb : ∀ x, 0 ≤ b x ∧ b x ≤ M)
    (hd : ∀ x, 0 ≤ d x) (hg : ∀ x, 0 ≤ g x)
    (hsrc : Integrable (fun x => chi x * (c x * h x)) mu)
    (hrest : Integrable (fun x => chi x * (d x * g x)) mu)
    (hprod : Integrable (fun x => b x * L x) mu)
    (hL : Integrable L mu)
    (green : (∫ x, chi x * (c x * h x + d x * g x) ∂mu) =
      ∫ x, b x * L x ∂mu) :
    (∫ x, chi x * (c x * h x) ∂mu) ≤ M * ∫ x, |L x| ∂mu := by
  have hle : (∫ x, chi x * (c x * h x) ∂mu) ≤
      ∫ x, chi x * (c x * h x + d x * g x) ∂mu := by
    simp_rw [mul_add]
    rw [integral_add hsrc hrest]
    have hnn : 0 ≤ ∫ x, chi x * (d x * g x) ∂mu :=
      integral_nonneg (fun x => mul_nonneg (hchi x) (mul_nonneg (hd x) (hg x)))
    linarith
  calc
    (∫ x, chi x * (c x * h x) ∂mu)
        ≤ ∫ x, b x * L x ∂mu := hle.trans_eq green
    _ ≤ ∫ x, M * |L x| ∂mu := by
      apply integral_mono hprod (hL.abs.const_mul M)
      intro x
      calc
        b x * L x ≤ b x * |L x| := mul_le_mul_of_nonneg_left (le_abs_self _) (hb x).1
        _ ≤ M * |L x| := mul_le_mul_of_nonneg_right (hb x).2 (abs_nonneg _)
    _ = M * ∫ x, |L x| ∂mu := integral_const_mul _ _

/-- Fatou transfers a uniform bound without assuming integrability of the limit. -/
theorem fatou_uniform_bound {F : ℕ → S → ℝ} {f : S → ℝ} {B : ℝ}
    (hF : ∀ n, Integrable (F n) mu)
    (hFpos : ∀ n x, 0 ≤ F n x)
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hbound : ∀ n, (∫ x, F n x ∂mu) ≤ B) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂mu) ≤ ENNReal.ofReal B := by
  have hlim' (x : S) : Tendsto (fun n => ENNReal.ofReal (F n x)) atTop
      (𝓝 (ENNReal.ofReal (f x))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hlim x)
  calc
    (∫⁻ x, ENNReal.ofReal (f x) ∂mu) =
        ∫⁻ x, liminf (fun n => ENNReal.ofReal (F n x)) atTop ∂mu := by
      apply lintegral_congr
      intro x
      exact (hlim' x).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂mu) atTop :=
      lintegral_liminf_le' (fun n => (hF n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    _ ≤ ENNReal.ofReal B := by
      apply liminf_le_of_frequently_le'
      apply Frequently.of_forall
      intro n
      rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (ae_of_all _ (hFpos n))]
      exact ENNReal.ofReal_le_ofReal (hbound n)

/-- The crucial positive-part area estimate, from explicitly stated regularisation data.

No distributional positivity or area bound is assumed. The analytic bridge that
supplies `green`, and the regularisation construction, are outside this file.
-/
theorem positive_part_area_bound
    {u h g chi L : S → ℝ} {b c d : ℕ → S → ℝ} {M : ℝ}
    (hchi : ∀ x, 0 ≤ chi x)
    (hsignPos : ∀ x, 0 < u x → 0 ≤ h x)
    (hsignNeg : ∀ x, u x ≤ 0 → h x ≤ 0)
    (hb : ∀ n x, 0 ≤ b n x ∧ b n x ≤ M)
    (hc : ∀ n x, 0 ≤ c n x)
    (hcZero : ∀ n x, u x ≤ 0 → c n x = 0)
    (hcLim : ∀ x, Tendsto (fun n => c n x) atTop (𝓝 (if 0 < u x then 1 else 0)))
    (hd : ∀ n x, 0 ≤ d n x) (hg : ∀ x, 0 ≤ g x)
    (hsrc : ∀ n, Integrable (fun x => chi x * (c n x * h x)) mu)
    (hrest : ∀ n, Integrable (fun x => chi x * (d n x * g x)) mu)
    (hprod : ∀ n, Integrable (fun x => b n x * L x) mu)
    (hL : Integrable L mu)
    (green : ∀ n, (∫ x, chi x * (c n x * h x + d n x * g x) ∂mu) =
      ∫ x, b n x * L x ∂mu) :
    (∫⁻ x, ENNReal.ofReal (chi x * max (h x) 0) ∂mu) ≤
      ENNReal.ofReal (M * ∫ x, |L x| ∂mu) := by
  apply fatou_uniform_bound hsrc
  · intro n x
    exact mul_nonneg (hchi x)
      (regularized_source_nonneg (hsignPos x) (hc n x) (hcZero n x))
  · intro x
    exact (regularized_source_tendsto (hsignPos x) (hsignNeg x) (hcLim x)).const_mul (chi x)
  · intro n
    exact smooth_cutoff_bound hchi (hb n) (hd n) hg
      (hsrc n) (hrest n) (hprod n) hL (green n)

end AreaDeficitCore

#print axioms AreaDeficitCore.curvature_sign
#print axioms AreaDeficitCore.primitive_bounds
#print axioms AreaDeficitCore.slope_scaled_tendsto
#print axioms AreaDeficitCore.smooth_cutoff_bound
#print axioms AreaDeficitCore.fatou_uniform_bound
#print axioms AreaDeficitCore.positive_part_area_bound
