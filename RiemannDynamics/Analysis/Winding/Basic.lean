/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Winding numbers of loops in the plane

The winding number of a closed continuous curve `γ : C(I, ℂ)` about a point
`q` not on the curve, defined through continuous logarithm lifts: any lift
`L` with `exp (L t) = γ t − q` changes by `2πi · m` over the interval for a
unique integer `m`, the winding number.

Lifts exist by factoring `γ − q` as modulus times unimodular part and lifting
the unimodular part through the circle covering `Circle.exp`; the increment
is lift-independent because two lifts differ by a continuous `2πiℤ`-valued
function on the connected interval, hence a constant.

The file provides the calculus consumed by the grid-homotopy development and
the covering-degree dichotomy: multiplicativity (windings add over pointwise
products), concatenation additivity, vanishing on balls, constancy on
connected sets avoiding the curve, homotopy invariance, and the polynomial
argument principle in winding form (the winding of `p ∘ γ` about `0` is the
root-multiset sum of windings of `γ` about the roots).
-/

open Complex Set unitInterval

namespace RiemannDynamics

/-- `L` is a continuous logarithm lift of `γ`: pointwise `exp (L t) = γ t`. -/
def IsLogLiftOf (L γ : C(I, ℂ)) : Prop :=
  ∀ t : I, Complex.exp (L t) = γ t

/-- Continuous nonvanishing curves on the interval admit continuous
logarithm lifts: lift the unimodular part `γ/‖γ‖` through the circle
covering `Circle.exp` (path lifting for covering maps) and add
`Real.log ‖γ‖`. -/
theorem exists_isLogLiftOf (γ : C(I, ℂ)) (hγ : ∀ t : I, γ t ≠ 0) :
    ∃ L : C(I, ℂ), IsLogLiftOf L γ := by
  have hnz : ∀ t : I, ‖γ t‖ ≠ 0 := fun t => norm_ne_zero_iff.2 (hγ t)
  have hden : ∀ t : I, (‖γ t‖ : ℂ) ≠ 0 := fun t => Complex.ofReal_ne_zero.2 (hnz t)
  have hmem : ∀ t : I, γ t / (‖γ t‖ : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by
    intro t
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      div_self (hnz t)]
  have hcont : Continuous fun t : I => γ t / (‖γ t‖ : ℂ) :=
    γ.continuous.div (Complex.continuous_ofReal.comp γ.continuous.norm) hden
  obtain ⟨θ, hθ, -⟩ := Circle.isCoveringMap_exp.exists_path_lifts
    (⟨fun t => ⟨γ t / (‖γ t‖ : ℂ), hmem t⟩, hcont.subtype_mk _⟩ : C(I, Circle))
    (Complex.arg (γ 0 / (‖γ 0‖ : ℂ)))
    (Circle.exp_arg ⟨γ 0 / (‖γ 0‖ : ℂ), hmem 0⟩).symm
  refine ⟨⟨fun t => (Real.log ‖γ t‖ : ℂ) + (θ t : ℂ) * Complex.I, ?_⟩, ?_⟩
  · exact (Complex.continuous_ofReal.comp (γ.continuous.norm.log hnz)).add
      ((Complex.continuous_ofReal.comp θ.continuous).mul continuous_const)
  · intro t
    have h3 := congr_fun hθ t
    have h4 : (Circle.exp (θ t) : ℂ) = γ t / (‖γ t‖ : ℂ) :=
      congrArg (fun z : Circle => (z : ℂ)) h3
    rw [Circle.coe_exp] at h4
    change Complex.exp ((Real.log ‖γ t‖ : ℂ) + (θ t : ℂ) * Complex.I) = γ t
    rw [Complex.exp_add, h4, ← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr (hγ t)),
      mul_comm, div_mul_cancel₀ _ (hden t)]

/-- The increment of a logarithm lift over the interval does not depend on
the choice of lift: two lifts differ by a continuous function with values in
the discrete set `2πiℤ`, hence by a constant. -/
theorem isLogLiftOf_increment_eq {γ L₁ L₂ : C(I, ℂ)}
    (h₁ : IsLogLiftOf L₁ γ) (h₂ : IsLogLiftOf L₂ γ) :
    L₁ 1 - L₁ 0 = L₂ 1 - L₂ 0 := by
  have hexp1 : ∀ t : I, Complex.exp (L₁ t - L₂ t) = 1 := by
    intro t
    have hne : γ t ≠ 0 := by rw [← h₁ t]; exact Complex.exp_ne_zero _
    rw [Complex.exp_sub, h₁ t, h₂ t, div_self hne]
  have hE : ∀ t : I, Complex.exp (L₁ t - L₂ t - (L₁ 0 - L₂ 0)) = 1 := by
    intro t
    rw [Complex.exp_sub, hexp1 t, hexp1 0, div_one]
  have hmem : ∀ t : I, ∃ n : ℤ,
      L₁ t - L₂ t - (L₁ 0 - L₂ 0) = n * (2 * Real.pi * Complex.I) := by
    intro t
    exact Complex.exp_eq_one_iff.mp (hE t)
  have hnorm2pi : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  have key : ∀ t : I, ‖L₁ t - L₂ t - (L₁ 0 - L₂ 0)‖ < 2 * Real.pi →
      L₁ t - L₂ t = L₁ 0 - L₂ 0 := by
    intro t ht
    obtain ⟨n, hn⟩ := hmem t
    have hn0 : n = 0 := by
      by_contra h0
      have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs h0
      have h2 : ‖L₁ t - L₂ t - (L₁ 0 - L₂ 0)‖ = |(n : ℝ)| * (2 * Real.pi) := by
        rw [hn, norm_mul, Complex.norm_intCast, hnorm2pi]
      rw [h2] at ht
      nlinarith [Real.two_pi_pos]
    rw [hn0, Int.cast_zero, zero_mul] at hn
    exact sub_eq_zero.mp hn
  have hS : IsClopen {t : I | L₁ t - L₂ t = L₁ 0 - L₂ 0} := by
    constructor
    · exact isClosed_eq ((map_continuous L₁).sub (map_continuous L₂)) continuous_const
    · have hset : {t : I | L₁ t - L₂ t = L₁ 0 - L₂ 0} =
          {t : I | ‖L₁ t - L₂ t - (L₁ 0 - L₂ 0)‖ < 2 * Real.pi} := by
        ext t
        simp only [mem_ofPred_eq]
        constructor
        · intro h
          rw [h, sub_self, norm_zero]
          exact Real.two_pi_pos
        · exact key t
      rw [hset]
      exact isOpen_lt
        ((((map_continuous L₁).sub (map_continuous L₂)).sub continuous_const).norm)
        continuous_const
  have huniv : {t : I | L₁ t - L₂ t = L₁ 0 - L₂ 0} = univ :=
    hS.eq_univ ⟨0, rfl⟩
  have h1 : L₁ 1 - L₂ 1 = L₁ 0 - L₂ 0 := by
    have hmem1 : (1 : I) ∈ {t : I | L₁ t - L₂ t = L₁ 0 - L₂ 0} := by
      rw [huniv]; trivial
    exact hmem1
  linear_combination h1

/-- The shifted curve `γ − q` as a continuous map. -/
noncomputable def shiftedCurve (γ : C(I, ℂ)) (q : ℂ) : C(I, ℂ) :=
  γ - ContinuousMap.const I q

open Classical in
/-- **Winding number** of a curve about a point, through logarithm lifts:
the unique integer `m` with `L 1 − L 0 = 2πi·m` for every logarithm lift `L`
of `γ − q`, when such an integer exists (it does exactly when `γ` is closed
and avoids `q`); junk value `0` otherwise. -/
noncomputable def windingNumber (γ : C(I, ℂ)) (q : ℂ) : ℤ :=
  if h : ∃ m : ℤ, ∀ L : C(I, ℂ), IsLogLiftOf L (shiftedCurve γ q) →
      L 1 - L 0 = 2 * Real.pi * Complex.I * m
  then h.choose else 0

/-- The defining property of the winding number: for a closed curve avoiding
`q`, every logarithm lift of `γ − q` increments by `2πi` times the winding
number. -/
theorem windingNumber_spec {γ : C(I, ℂ)} {q : ℂ}
    (hcl : γ 0 = γ 1) (hq : ∀ t : I, γ t ≠ q)
    {L : C(I, ℂ)} (hL : IsLogLiftOf L (shiftedCurve γ q)) :
    L 1 - L 0 = 2 * Real.pi * Complex.I * windingNumber γ q := by
  have happ : ∀ t : I, shiftedCurve γ q t = γ t - q := by
    intro t
    simp [shiftedCurve]
  have hδ : ∀ t : I, shiftedCurve γ q t ≠ 0 := by
    intro t
    rw [happ t]
    exact sub_ne_zero.mpr (hq t)
  obtain ⟨L₀, hL₀⟩ := exists_isLogLiftOf (shiftedCurve γ q) hδ
  have hδcl : shiftedCurve γ q 1 = shiftedCurve γ q 0 := by
    rw [happ 0, happ 1, hcl]
  have hexp : Complex.exp (L₀ 1 - L₀ 0) = 1 := by
    rw [Complex.exp_sub, hL₀ 1, hL₀ 0, hδcl, div_self (hδ 0)]
  obtain ⟨m₀, hm₀⟩ := Complex.exp_eq_one_iff.mp hexp
  have hP : ∃ m : ℤ, ∀ L' : C(I, ℂ), IsLogLiftOf L' (shiftedCurve γ q) →
      L' 1 - L' 0 = 2 * Real.pi * Complex.I * m := by
    refine ⟨m₀, fun L' hL' => ?_⟩
    rw [isLogLiftOf_increment_eq hL' hL₀, hm₀]
    ring
  have hwn : windingNumber γ q = hP.choose := by
    unfold windingNumber
    exact dite_eq_left hP
  rw [hwn]
  exact hP.choose_spec L hL

/-- Winding numbers add over pointwise products of closed nonvanishing
curves (about `0`): logarithm lifts add. -/
theorem windingNumber_mul (γ₁ γ₂ : C(I, ℂ))
    (hcl₁ : γ₁ 0 = γ₁ 1) (hcl₂ : γ₂ 0 = γ₂ 1)
    (h₁ : ∀ t : I, γ₁ t ≠ 0) (h₂ : ∀ t : I, γ₂ t ≠ 0) :
    windingNumber (γ₁ * γ₂) 0 = windingNumber γ₁ 0 + windingNumber γ₂ 0 := by
  obtain ⟨L₁, hL₁⟩ := exists_isLogLiftOf γ₁ h₁
  obtain ⟨L₂, hL₂⟩ := exists_isLogLiftOf γ₂ h₂
  have hlift₁ : IsLogLiftOf L₁ (shiftedCurve γ₁ 0) := by
    intro t
    simpa [shiftedCurve] using hL₁ t
  have hlift₂ : IsLogLiftOf L₂ (shiftedCurve γ₂ 0) := by
    intro t
    simpa [shiftedCurve] using hL₂ t
  have hlift₁₂ : IsLogLiftOf (L₁ + L₂) (shiftedCurve (γ₁ * γ₂) 0) := by
    intro t
    simp only [shiftedCurve, ContinuousMap.sub_apply, ContinuousMap.const_apply,
      ContinuousMap.add_apply, ContinuousMap.mul_apply, sub_zero, Complex.exp_add,
      hL₁ t, hL₂ t]
  have hspec₁ := windingNumber_spec hcl₁ h₁ hlift₁
  have hspec₂ := windingNumber_spec hcl₂ h₂ hlift₂
  have hcl₁₂ : (γ₁ * γ₂) 0 = (γ₁ * γ₂) 1 := by
    simp only [ContinuousMap.mul_apply, hcl₁, hcl₂]
  have hq₁₂ : ∀ t : I, (γ₁ * γ₂) t ≠ (0 : ℂ) := fun t => by
    simp only [ContinuousMap.mul_apply]
    exact mul_ne_zero (h₁ t) (h₂ t)
  have hspec₁₂ := windingNumber_spec hcl₁₂ hq₁₂ hlift₁₂
  have hsum : (L₁ + L₂) 1 - (L₁ + L₂) 0 = (L₁ 1 - L₁ 0) + (L₂ 1 - L₂ 0) := by
    simp only [ContinuousMap.add_apply]
    ring
  rw [hsum, hspec₁, hspec₂] at hspec₁₂
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have h' : 2 * (Real.pi : ℂ) * Complex.I *
        ((windingNumber γ₁ 0 : ℂ) + (windingNumber γ₂ 0 : ℂ)) =
      2 * (Real.pi : ℂ) * Complex.I * (windingNumber (γ₁ * γ₂) 0 : ℂ) := by
    rw [mul_add]
    exact hspec₁₂
  exact_mod_cast (mul_left_cancel₀ hπ h').symm

/-- Constant curves have winding number zero about every point they avoid. -/
theorem windingNumber_const (c q : ℂ) (hcq : c ≠ q) :
    windingNumber (ContinuousMap.const I c) q = 0 := by
  have hne : c - q ≠ 0 := sub_ne_zero.mpr hcq
  have hlift : IsLogLiftOf (ContinuousMap.const I (Complex.log (c - q)))
      (shiftedCurve (ContinuousMap.const I c) q) := by
    intro t
    simp [shiftedCurve, Complex.exp_log hne]
  have hspec := windingNumber_spec (γ := ContinuousMap.const I c) (q := q)
    rfl (fun _ => hcq) hlift
  simp only [ContinuousMap.const_apply, sub_self] at hspec
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hm := (mul_eq_zero.mp hspec.symm).resolve_left hπ
  exact_mod_cast hm

/-- A closed curve with values in a ball winds zero times about any point
outside the ball: the shifted curve takes values in an open half-plane,
where a branch of the logarithm is continuous. -/
theorem windingNumber_eq_zero_of_ball {γ : C(I, ℂ)} {c q : ℂ} {r : ℝ}
    (hcl : γ 0 = γ 1) (hγ : ∀ t : I, γ t ∈ Metric.ball c r)
    (hq : q ∉ Metric.ball c r) :
    windingNumber γ q = 0 := by
  -- the curve avoids `q`
  have hne : ∀ t : I, γ t ≠ q := by
    intro t h
    exact hq (h ▸ hγ t)
  -- the center-to-base distance dominates the radius, which is positive
  have hrle : r ≤ ‖c - q‖ := by
    have h1 : ¬ dist q c < r := fun h' => hq (Metric.mem_ball.mpr h')
    rw [dist_eq_norm] at h1
    have h2 := not_lt.mp h1
    rwa [norm_sub_rev] at h2
  have hd0 : (0 : ℝ) < ‖c - q‖ := by
    have h0 : (0 : ℝ) ≤ dist (γ 0) c := dist_nonneg
    have h1 : dist (γ 0) c < r := Metric.mem_ball.mp (hγ 0)
    linarith
  have hd : c - q ≠ 0 := by
    intro h
    rw [h, norm_zero] at hd0
    exact lt_irrefl _ hd0
  -- the normalized shifted curve stays in the disk about `1`
  have hcont_u : Continuous fun t : I => (γ t - q) / (c - q) :=
    (γ.continuous.sub continuous_const).div_const _
  obtain ⟨u, hu_apply⟩ : ∃ u : C(I, ℂ), ∀ t : I,
      u t = (γ t - q) / (c - q) :=
    ⟨⟨fun t => (γ t - q) / (c - q), hcont_u⟩, fun t => rfl⟩
  have hu_near : ∀ t : I, ‖u t - 1‖ < 1 := by
    intro t
    have h1 : u t - 1 = (γ t - c) / (c - q) := by
      rw [hu_apply t, div_sub_one hd]
      ring_nf
    have h2 : ‖γ t - c‖ < r := by
      have h3 := Metric.mem_ball.mp (hγ t)
      rwa [dist_eq_norm] at h3
    rw [h1, norm_div]
    exact (div_lt_one hd0).mpr (lt_of_lt_of_le h2 hrle)
  have hu_re : ∀ t : I, 0 < (u t).re := by
    intro t
    have h1 : |(u t).re - 1| ≤ ‖u t - 1‖ := by
      have h2 := Complex.abs_re_le_norm (u t - 1)
      simpa [Complex.sub_re, Complex.one_re] using h2
    have h3 := abs_lt.mp (lt_of_le_of_lt h1 (hu_near t))
    linarith [h3.1]
  have hu_ne : ∀ t : I, u t ≠ 0 := by
    intro t h
    have h2 := hu_re t
    rw [h] at h2
    simp at h2
  -- a continuous logarithm of the normalized curve
  have hcont_log : Continuous fun t : I => Complex.log (u t) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact ContinuousAt.clog u.continuous.continuousAt
      (Complex.mem_slitPlane_iff.mpr (Or.inl (hu_re t)))
  obtain ⟨L, hL_apply⟩ : ∃ L : C(I, ℂ), ∀ t : I,
      L t = Complex.log (u t) + Complex.log (c - q) :=
    ⟨⟨fun t => Complex.log (u t) + Complex.log (c - q),
      hcont_log.add continuous_const⟩, fun t => rfl⟩
  have hshift : ∀ t : I, shiftedCurve γ q t = γ t - q := fun t => rfl
  have hL : IsLogLiftOf L (shiftedCurve γ q) := by
    intro t
    rw [hL_apply t, Complex.exp_add, Complex.exp_log (hu_ne t),
      Complex.exp_log hd, hshift t, hu_apply t]
    exact div_mul_cancel₀ _ hd
  have hspec := windingNumber_spec hcl hne hL
  -- the lift has zero increment since the curve is closed
  have hL10 : L 1 - L 0 = 0 := by
    rw [hL_apply 1, hL_apply 0, hu_apply 1, hu_apply 0, ← hcl]
    ring
  rw [hL10] at hspec
  have hm := (mul_eq_zero.mp hspec.symm).resolve_left Complex.two_pi_I_ne_zero
  exact_mod_cast hm

/-- The winding number is constant on preconnected sets of base points
avoiding the curve: local constancy by the division trick (the quotient of
nearby shifted curves stays near `1`, where the principal logarithm lifts),
then the clopen argument. -/
theorem windingNumber_eq_of_preconnected {γ : C(I, ℂ)}
    (hcl : γ 0 = γ 1) {C : Set ℂ} (hC : IsPreconnected C)
    (hdisj : ∀ t : I, γ t ∉ C) {q₁ q₂ : ℂ} (hq₁ : q₁ ∈ C) (hq₂ : q₂ ∈ C) :
    windingNumber γ q₁ = windingNumber γ q₂ := by
  -- Perturbation engine for the base point: moving the base point by less
  -- than its distance to the curve does not change the winding number.
  have key : ∀ q₀ q : ℂ, (∀ t : I, ‖q - q₀‖ < ‖γ t - q₀‖) →
      windingNumber γ q₀ = windingNumber γ q := by
    intro q₀ q hlt
    have hne₀ : ∀ t : I, γ t ≠ q₀ := by
      intro t h
      have h0 := hlt t
      rw [h, sub_self, norm_zero] at h0
      exact absurd h0 (not_lt.mpr (norm_nonneg _))
    have hne₀' : ∀ t : I, γ t - q₀ ≠ 0 := fun t => sub_ne_zero.mpr (hne₀ t)
    have hne : ∀ t : I, γ t ≠ q := by
      intro t h
      have h0 := hlt t
      rw [← h] at h0
      exact lt_irrefl _ h0
    -- the quotient curve `(γ - q)/(γ - q₀)` stays in the disk about `1`
    have hcont_u : Continuous fun t : I => (γ t - q) / (γ t - q₀) :=
      (γ.continuous.sub continuous_const).div
        (γ.continuous.sub continuous_const) fun t => hne₀' t
    obtain ⟨u, hu_apply⟩ : ∃ u : C(I, ℂ), ∀ t : I,
        u t = (γ t - q) / (γ t - q₀) :=
      ⟨⟨fun t => (γ t - q) / (γ t - q₀), hcont_u⟩, fun t => rfl⟩
    have hu_near : ∀ t : I, ‖u t - 1‖ < 1 := by
      intro t
      have h1 : u t - 1 = (q₀ - q) / (γ t - q₀) := by
        rw [hu_apply t, div_sub_one (hne₀' t)]
        ring_nf
      rw [h1, norm_div, norm_sub_rev]
      exact (div_lt_one (norm_pos_iff.mpr (hne₀' t))).mpr (hlt t)
    have hu_re : ∀ t : I, 0 < (u t).re := by
      intro t
      have h1 : |(u t).re - 1| ≤ ‖u t - 1‖ := by
        have h2 := Complex.abs_re_le_norm (u t - 1)
        simpa [Complex.sub_re, Complex.one_re] using h2
      have h3 := abs_lt.mp (lt_of_le_of_lt h1 (hu_near t))
      linarith [h3.1]
    have hu_ne : ∀ t : I, u t ≠ 0 := by
      intro t h
      have h2 := hu_re t
      rw [h] at h2
      simp at h2
    -- a continuous logarithm of the quotient
    have hcont_log : Continuous fun t : I => Complex.log (u t) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact ContinuousAt.clog u.continuous.continuousAt
        (Complex.mem_slitPlane_iff.mpr (Or.inl (hu_re t)))
    obtain ⟨Lu, hLu_apply⟩ : ∃ Lu : C(I, ℂ), ∀ t : I,
        Lu t = Complex.log (u t) :=
      ⟨⟨fun t => Complex.log (u t), hcont_log⟩, fun t => rfl⟩
    have hshift₀ : ∀ t : I, shiftedCurve γ q₀ t = γ t - q₀ := fun t => rfl
    have hshift : ∀ t : I, shiftedCurve γ q t = γ t - q := fun t => rfl
    -- lift of the curve shifted by `q₀`; add the quotient logarithm to lift
    -- the curve shifted by `q`
    obtain ⟨L₀, hL₀⟩ := exists_isLogLiftOf (shiftedCurve γ q₀)
      (fun t => by rw [hshift₀ t]; exact hne₀' t)
    have hL : IsLogLiftOf (L₀ + Lu) (shiftedCurve γ q) := by
      intro t
      have happ : (L₀ + Lu) t = L₀ t + Lu t := rfl
      rw [happ, Complex.exp_add, hL₀ t, hLu_apply t,
        Complex.exp_log (hu_ne t), hshift₀ t, hshift t, hu_apply t,
        mul_comm]
      exact div_mul_cancel₀ _ (hne₀' t)
    have hspec₀ := windingNumber_spec hcl hne₀ hL₀
    have hspec := windingNumber_spec hcl hne hL
    -- the quotient is a closed curve, so its logarithm has zero increment
    have hu01 : u 1 = u 0 := by
      rw [hu_apply 1, hu_apply 0, ← hcl]
    have hincr : (L₀ + Lu) 1 - (L₀ + Lu) 0 = L₀ 1 - L₀ 0 := by
      have e1 : (L₀ + Lu) 1 = L₀ 1 + Lu 1 := rfl
      have e0 : (L₀ + Lu) 0 = L₀ 0 + Lu 0 := rfl
      rw [e1, e0, hLu_apply 1, hLu_apply 0, hu01]
      ring
    rw [hspec, hspec₀] at hincr
    have hcast := mul_left_cancel₀ Complex.two_pi_I_ne_zero hincr
    exact_mod_cast hcast.symm
  -- Local constancy: around any base point off the curve, the winding
  -- number is constant on the ball of radius the distance to the curve.
  have hloc : ∀ q₀ : ℂ, q₀ ∉ Set.range γ → ∃ r > 0, ∀ q : ℂ, dist q q₀ < r →
      q ∉ Set.range γ ∧ windingNumber γ q = windingNumber γ q₀ := by
    intro q₀ hq₀
    obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
      (Continuous.continuousOn ((γ.continuous.sub continuous_const).norm) :
        ContinuousOn (fun t : I => ‖γ t - q₀‖) Set.univ)
    have hr : 0 < ‖γ t₀ - q₀‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hq₀ ⟨t₀, h⟩)
    refine ⟨‖γ t₀ - q₀‖, hr, fun q hq => ?_⟩
    have hlt : ∀ t : I, ‖q - q₀‖ < ‖γ t - q₀‖ := by
      intro t
      have h1 : ‖q - q₀‖ < ‖γ t₀ - q₀‖ := by rwa [← dist_eq_norm]
      exact lt_of_lt_of_le h1 (isMinOn_iff.mp ht₀ t (Set.mem_univ t))
    refine ⟨?_, (key q₀ q hlt).symm⟩
    rintro ⟨t, ht⟩
    have h2 := hlt t
    rw [ht] at h2
    exact lt_irrefl _ h2
  -- The two relatively open pieces: equal and unequal winding number.
  have hUopen : IsOpen {q : ℂ | q ∉ Set.range γ ∧
      windingNumber γ q = windingNumber γ q₁} := by
    rw [Metric.isOpen_iff]
    rintro q₀ ⟨hq₀, hw₀⟩
    obtain ⟨r, hr, hball⟩ := hloc q₀ hq₀
    refine ⟨r, hr, fun q hq => ?_⟩
    have h1 := hball q (Metric.mem_ball.mp hq)
    exact ⟨h1.1, h1.2.trans hw₀⟩
  have hVopen : IsOpen {q : ℂ | q ∉ Set.range γ ∧
      ¬ windingNumber γ q = windingNumber γ q₁} := by
    rw [Metric.isOpen_iff]
    rintro q₀ ⟨hq₀, hw₀⟩
    obtain ⟨r, hr, hball⟩ := hloc q₀ hq₀
    refine ⟨r, hr, fun q hq => ?_⟩
    have h1 := hball q (Metric.mem_ball.mp hq)
    exact ⟨h1.1, fun h => hw₀ (h1.2.symm.trans h)⟩
  -- `C` avoids the curve, so it is covered by the two pieces.
  have hCr : ∀ q ∈ C, q ∉ Set.range γ := by
    rintro q hq ⟨t, ht⟩
    exact hdisj t (by rw [ht]; exact hq)
  have hcover : C ⊆ {q : ℂ | q ∉ Set.range γ ∧
        windingNumber γ q = windingNumber γ q₁} ∪
      {q : ℂ | q ∉ Set.range γ ∧
        ¬ windingNumber γ q = windingNumber γ q₁} := by
    intro q hq
    by_cases h : windingNumber γ q = windingNumber γ q₁
    · exact Or.inl ⟨hCr q hq, h⟩
    · exact Or.inr ⟨hCr q hq, h⟩
  -- The preconnected set cannot meet both pieces, which are disjoint.
  by_contra hw
  have h1 : (C ∩ {q : ℂ | q ∉ Set.range γ ∧
      windingNumber γ q = windingNumber γ q₁}).Nonempty :=
    ⟨q₁, hq₁, hCr q₁ hq₁, rfl⟩
  have h2 : (C ∩ {q : ℂ | q ∉ Set.range γ ∧
      ¬ windingNumber γ q = windingNumber γ q₁}).Nonempty :=
    ⟨q₂, hq₂, hCr q₂ hq₂, fun h => hw h.symm⟩
  obtain ⟨x, -, hxU, hxV⟩ := hC _ _ hUopen hVopen hcover h1 h2
  exact hxV.2 hxU.2

/-- Winding numbers are invariant under homotopy of closed curves relative
to the endpoints within the complement of the base point: lift the homotopy
through the exponential and use discreteness of the increment. -/
theorem windingNumber_eq_of_homotopicRel {γ₁ γ₂ : C(I, ℂ)} {q : ℂ}
    (hcl₁ : γ₁ 0 = γ₁ 1)
    (H : ContinuousMap.HomotopyRel γ₁ γ₂ {0, 1})
    (hH : ∀ (t : I) (s : I), H (t, s) ≠ q) :
    windingNumber γ₁ q = windingNumber γ₂ q := by
  -- Perturbation engine: a uniform perturbation smaller than the distance
  -- to the base point does not change the winding number.
  have key : ∀ δ₁ δ₂ : C(I, ℂ), δ₁ 0 = δ₁ 1 → δ₂ 0 = δ₂ 1 →
      (∀ t : I, ‖δ₂ t - δ₁ t‖ < ‖δ₁ t - q‖) →
      windingNumber δ₁ q = windingNumber δ₂ q := by
    intro δ₁ δ₂ hc₁ hc₂ hlt
    have hne₁ : ∀ t : I, δ₁ t ≠ q := by
      intro t h
      have h0 := hlt t
      rw [h, sub_self, norm_zero] at h0
      exact absurd h0 (not_lt.mpr (norm_nonneg _))
    have hne₁' : ∀ t : I, δ₁ t - q ≠ 0 := fun t => sub_ne_zero.mpr (hne₁ t)
    have hne₂ : ∀ t : I, δ₂ t ≠ q := by
      intro t h
      have h0 := hlt t
      rw [h, norm_sub_rev] at h0
      exact lt_irrefl _ h0
    -- the quotient curve `(δ₂ - q)/(δ₁ - q)` stays in the disk about `1`
    have hcont_u : Continuous fun t : I => (δ₂ t - q) / (δ₁ t - q) :=
      (δ₂.continuous.sub continuous_const).div
        (δ₁.continuous.sub continuous_const) fun t => hne₁' t
    obtain ⟨u, hu_apply⟩ : ∃ u : C(I, ℂ), ∀ t : I,
        u t = (δ₂ t - q) / (δ₁ t - q) :=
      ⟨⟨fun t => (δ₂ t - q) / (δ₁ t - q), hcont_u⟩, fun t => rfl⟩
    have hu_near : ∀ t : I, ‖u t - 1‖ < 1 := by
      intro t
      have h1 : u t - 1 = (δ₂ t - δ₁ t) / (δ₁ t - q) := by
        rw [hu_apply t, div_sub_one (hne₁' t)]
        ring_nf
      rw [h1, norm_div]
      exact (div_lt_one (norm_pos_iff.mpr (hne₁' t))).mpr (hlt t)
    have hu_re : ∀ t : I, 0 < (u t).re := by
      intro t
      have h1 : |(u t).re - 1| ≤ ‖u t - 1‖ := by
        have h2 := Complex.abs_re_le_norm (u t - 1)
        simpa [Complex.sub_re, Complex.one_re] using h2
      have h3 := abs_lt.mp (lt_of_le_of_lt h1 (hu_near t))
      linarith [h3.1]
    have hu_ne : ∀ t : I, u t ≠ 0 := by
      intro t h
      have h2 := hu_re t
      rw [h] at h2
      simp at h2
    -- a continuous logarithm of the quotient
    have hcont_log : Continuous fun t : I => Complex.log (u t) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact ContinuousAt.clog u.continuous.continuousAt
        (Complex.mem_slitPlane_iff.mpr (Or.inl (hu_re t)))
    obtain ⟨Lu, hLu_apply⟩ : ∃ Lu : C(I, ℂ), ∀ t : I,
        Lu t = Complex.log (u t) :=
      ⟨⟨fun t => Complex.log (u t), hcont_log⟩, fun t => rfl⟩
    have hshift₁ : ∀ t : I, shiftedCurve δ₁ q t = δ₁ t - q := fun t => rfl
    have hshift₂ : ∀ t : I, shiftedCurve δ₂ q t = δ₂ t - q := fun t => rfl
    -- lift of the first shifted curve; add the quotient logarithm to lift
    -- the second
    obtain ⟨L₁, hL₁⟩ := exists_isLogLiftOf (shiftedCurve δ₁ q)
      (fun t => by rw [hshift₁ t]; exact hne₁' t)
    have hL₂ : IsLogLiftOf (L₁ + Lu) (shiftedCurve δ₂ q) := by
      intro t
      have happ : (L₁ + Lu) t = L₁ t + Lu t := rfl
      rw [happ, Complex.exp_add, hL₁ t, hLu_apply t,
        Complex.exp_log (hu_ne t), hshift₁ t, hshift₂ t, hu_apply t,
        mul_comm]
      exact div_mul_cancel₀ _ (hne₁' t)
    have hspec₁ := windingNumber_spec hc₁ hne₁ hL₁
    have hspec₂ := windingNumber_spec hc₂ hne₂ hL₂
    -- the quotient is a closed curve, so its logarithm has zero increment
    have hu01 : u 1 = u 0 := by
      rw [hu_apply 1, hu_apply 0, ← hc₁, ← hc₂]
    have hincr : (L₁ + Lu) 1 - (L₁ + Lu) 0 = L₁ 1 - L₁ 0 := by
      have e1 : (L₁ + Lu) 1 = L₁ 1 + Lu 1 := rfl
      have e0 : (L₁ + Lu) 0 = L₁ 0 + Lu 0 := rfl
      rw [e1, e0, hLu_apply 1, hLu_apply 0, hu01]
      ring
    rw [hspec₂, hspec₁] at hincr
    have hcast := mul_left_cancel₀ Complex.two_pi_I_ne_zero hincr
    exact_mod_cast hcast.symm
  -- The family of intermediate curves of the homotopy.
  have h01 : (0 : I) ∈ ({0, 1} : Set I) := Set.mem_insert 0 {1}
  have h11 : (1 : I) ∈ ({0, 1} : Set I) := Set.mem_insert_of_mem 0 rfl
  obtain ⟨G, hGapp⟩ : ∃ G : I → C(I, ℂ), ∀ s t : I, G s t = H (s, t) :=
    ⟨fun s => H.toContinuousMap.curry s, fun s t => rfl⟩
  have hGcl : ∀ s : I, G s 0 = G s 1 := by
    intro s
    rw [hGapp s 0, hGapp s 1, H.eq_fst s h01, H.eq_fst s h11, hcl₁]
  have hGne : ∀ s t : I, G s t ≠ q := by
    intro s t
    rw [hGapp s t]
    exact hH s t
  -- Local constancy of the winding number along the homotopy: near any
  -- homotopy time the curves stay uniformly closer to each other than to `q`.
  have hloc : ∀ s₀ : I, ∀ᶠ s in nhds s₀,
      windingNumber (G s) q = windingNumber (G s₀) q := by
    intro s₀
    obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
      (Continuous.continuousOn
        (((G s₀).continuous.sub continuous_const).norm) :
        ContinuousOn (fun t : I => ‖G s₀ t - q‖) Set.univ)
    have hε : 0 < ‖G s₀ t₀ - q‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (hGne s₀ t₀))
    have hUopen : IsOpen {p : I × I | ‖H p - G s₀ p.2‖ < ‖G s₀ t₀ - q‖} :=
      isOpen_lt (Continuous.norm ((map_continuous H).sub
        ((map_continuous (G s₀)).comp continuous_snd))) continuous_const
    have hsub : ({s₀} : Set I) ×ˢ (Set.univ : Set I) ⊆
        {p : I × I | ‖H p - G s₀ p.2‖ < ‖G s₀ t₀ - q‖} := by
      rintro ⟨s, t⟩ ⟨hs, -⟩
      rw [Set.mem_singleton_iff] at hs
      subst hs
      change ‖H (s, t) - G s t‖ < ‖G s t₀ - q‖
      rw [← hGapp s t, sub_self, norm_zero]
      exact hε
    obtain ⟨V, W, hVopen, -, hV, hW, hVW⟩ :=
      generalized_tube_lemma isCompact_singleton isCompact_univ hUopen hsub
    have hs₀V : s₀ ∈ V := hV rfl
    filter_upwards [hVopen.mem_nhds hs₀V] with s hs
    refine (key (G s₀) (G s) (hGcl s₀) (hGcl s) fun t => ?_).symm
    have hmem : (s, t) ∈ {p : I × I | ‖H p - G s₀ p.2‖ < ‖G s₀ t₀ - q‖} :=
      hVW (Set.mem_prod.mpr ⟨hs, hW (Set.mem_univ t)⟩)
    have hmem' : ‖H (s, t) - G s₀ t‖ < ‖G s₀ t₀ - q‖ := hmem
    rw [hGapp s t]
    exact lt_of_lt_of_le hmem' (isMinOn_iff.mp ht₀ t (Set.mem_univ t))
  -- The winding number is locally constant, hence constant on the
  -- connected interval: the level set of the initial value is clopen.
  have hAopen : IsOpen {s : I |
      windingNumber (G s) q = windingNumber (G 0) q} := by
    rw [isOpen_iff_mem_nhds]
    intro s₀ hs₀
    have hs₀' : windingNumber (G s₀) q = windingNumber (G 0) q := hs₀
    exact Filter.mem_of_superset (hloc s₀)
      fun s (hs : windingNumber (G s) q = windingNumber (G s₀) q) =>
        show windingNumber (G s) q = windingNumber (G 0) q from
          hs.trans hs₀'
  have hBopen : IsOpen {s : I |
      ¬ windingNumber (G s) q = windingNumber (G 0) q} := by
    rw [isOpen_iff_mem_nhds]
    intro s₀ hs₀
    have hs₀' : ¬ windingNumber (G s₀) q = windingNumber (G 0) q := hs₀
    exact Filter.mem_of_superset (hloc s₀)
      fun s (hs : windingNumber (G s) q = windingNumber (G s₀) q) =>
        show ¬ windingNumber (G s) q = windingNumber (G 0) q from
          fun h => hs₀' (hs ▸ h)
  have hclopen : IsClopen {s : I |
      windingNumber (G s) q = windingNumber (G 0) q} := by
    constructor
    · rw [← isOpen_compl_iff]
      exact hBopen
    · exact hAopen
  have huniv := hclopen.eq_univ ⟨0, rfl⟩
  have hconst : windingNumber (G 1) q = windingNumber (G 0) q := by
    have h1A : (1 : I) ∈ {s : I |
        windingNumber (G s) q = windingNumber (G 0) q} := by
      rw [huniv]
      exact Set.mem_univ 1
    exact h1A
  have hG0 : G 0 = γ₁ := by
    ext t
    rw [hGapp 0 t]
    exact H.apply_zero t
  have hG1 : G 1 = γ₂ := by
    ext t
    rw [hGapp 1 t]
    exact H.apply_one t
  rw [← hG0, ← hG1]
  exact hconst.symm

/-- Winding numbers add under concatenation of loops at a common
basepoint. -/
theorem windingNumber_trans {a : ℂ} (p₁ p₂ : Path a a) {q : ℂ}
    (h₁ : ∀ t : I, p₁ t ≠ q) (h₂ : ∀ t : I, p₂ t ≠ q) :
    windingNumber (p₁.trans p₂).toContinuousMap q =
      windingNumber p₁.toContinuousMap q +
        windingNumber p₂.toContinuousMap q := by
  -- The shifted legs do not vanish.
  have hne₁ : ∀ t : I, shiftedCurve p₁.toContinuousMap q t ≠ 0 := by
    intro t
    simp only [shiftedCurve, ContinuousMap.sub_apply, ContinuousMap.const_apply,
      Path.coe_toContinuousMap]
    exact sub_ne_zero.mpr (h₁ t)
  have hne₂ : ∀ t : I, shiftedCurve p₂.toContinuousMap q t ≠ 0 := by
    intro t
    simp only [shiftedCurve, ContinuousMap.sub_apply, ContinuousMap.const_apply,
      Path.coe_toContinuousMap]
    exact sub_ne_zero.mpr (h₂ t)
  -- Logarithm lifts of the two shifted legs.
  obtain ⟨L₁, hL₁⟩ := exists_isLogLiftOf _ hne₁
  obtain ⟨L₂, hL₂⟩ := exists_isLogLiftOf _ hne₂
  have hL₁' : ∀ t : I, Complex.exp (L₁ t) = p₁ t - q := by
    intro t
    simpa only [shiftedCurve, ContinuousMap.sub_apply, ContinuousMap.const_apply,
      Path.coe_toContinuousMap] using hL₁ t
  have hL₂' : ∀ t : I, Complex.exp (L₂ t) = p₂ t - q := by
    intro t
    simpa only [shiftedCurve, ContinuousMap.sub_apply, ContinuousMap.const_apply,
      Path.coe_toContinuousMap] using hL₂ t
  -- The seam constant exponentiates to `1`.
  have haq : a - q ≠ 0 := sub_ne_zero.mpr (by simpa using h₁ 0)
  have hc : Complex.exp (L₁ 1 - L₂ 0) = 1 := by
    rw [Complex.exp_sub, hL₁' 1, hL₂' 0]
    simp only [Path.target, Path.source]
    exact div_self haq
  -- The adjusted second lift still lifts the second shifted leg.
  have hL₂c : ∀ t : I,
      Complex.exp ((L₂ + ContinuousMap.const I (L₁ 1 - L₂ 0)) t) = p₂ t - q := by
    intro t
    simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
    rw [Complex.exp_add, hc, mul_one, hL₂' t]
  have hstart : (L₂ + ContinuousMap.const I (L₁ 1 - L₂ 0)) 0 = L₁ 1 := by
    simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
    ring
  -- Glue the lifts along the seam into a lift of the concatenated shifted loop.
  obtain ⟨L, hLlift, hL0, hL1⟩ :
      ∃ L : C(I, ℂ), IsLogLiftOf L (shiftedCurve (p₁.trans p₂).toContinuousMap q) ∧
        L 0 = L₁ 0 ∧ L 1 = L₂ 1 + (L₁ 1 - L₂ 0) := by
    refine ⟨((⟨L₁, rfl, rfl⟩ : Path (L₁ 0) (L₁ 1)).trans
        (⟨L₂ + ContinuousMap.const I (L₁ 1 - L₂ 0), hstart, rfl⟩ :
          Path (L₁ 1) ((L₂ + ContinuousMap.const I (L₁ 1 - L₂ 0)) 1))).toContinuousMap,
      ?_, ?_, ?_⟩
    · intro t
      simp only [shiftedCurve, ContinuousMap.sub_apply, ContinuousMap.const_apply,
        Path.coe_toContinuousMap]
      rw [Path.trans_apply, Path.trans_apply]
      split_ifs with ht
      · exact hL₁' _
      · exact hL₂c _
    · simp
    · simp
  -- Closedness and avoidance for the three loops.
  have hcl : (p₁.trans p₂).toContinuousMap 0 = (p₁.trans p₂).toContinuousMap 1 := by simp
  have hq' : ∀ t : I, (p₁.trans p₂).toContinuousMap t ≠ q := by
    intro t
    simp only [Path.coe_toContinuousMap]
    rw [Path.trans_apply]
    split_ifs with ht
    · exact h₁ _
    · exact h₂ _
  have hcl₁ : p₁.toContinuousMap 0 = p₁.toContinuousMap 1 := by simp
  have hq₁ : ∀ t : I, p₁.toContinuousMap t ≠ q := by intro t; simpa using h₁ t
  have hcl₂ : p₂.toContinuousMap 0 = p₂.toContinuousMap 1 := by simp
  have hq₂ : ∀ t : I, p₂.toContinuousMap t ≠ q := by intro t; simpa using h₂ t
  -- Pin the three winding numbers by the lift increments.
  have hw := windingNumber_spec hcl hq' hLlift
  have hw₁ := windingNumber_spec hcl₁ hq₁ hL₁
  have hw₂ := windingNumber_spec hcl₂ hq₂ hL₂
  rw [hL1, hL0] at hw
  have h2πi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have key : (2 * Real.pi * Complex.I) *
        ((windingNumber (p₁.trans p₂).toContinuousMap q : ℤ) : ℂ) =
      (2 * Real.pi * Complex.I) *
        ((windingNumber p₁.toContinuousMap q +
          windingNumber p₂.toContinuousMap q : ℤ) : ℂ) := by
    rw [Int.cast_add, mul_add, ← hw₁, ← hw₂, ← hw]
    ring
  exact_mod_cast mul_left_cancel₀ h2πi key

/-- Reversing a loop negates its winding number. -/
theorem windingNumber_symm {a : ℂ} (p : Path a a) {q : ℂ}
    (h : ∀ t : I, p t ≠ q) :
    windingNumber p.symm.toContinuousMap q =
      -windingNumber p.toContinuousMap q := by
  have hne : ∀ t : I, shiftedCurve p.toContinuousMap q t ≠ 0 := by
    intro t
    simp only [shiftedCurve, ContinuousMap.sub_apply, ContinuousMap.const_apply,
      Path.coe_toContinuousMap]
    exact sub_ne_zero.mpr (h t)
  obtain ⟨L, hL⟩ := exists_isLogLiftOf _ hne
  have hL' : ∀ t : I, Complex.exp (L t) = p t - q := by
    intro t
    simpa only [shiftedCurve, ContinuousMap.sub_apply, ContinuousMap.const_apply,
      Path.coe_toContinuousMap] using hL t
  -- The reversed lift lifts the reversed shifted loop.
  have hLs : IsLogLiftOf (L.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩)
      (shiftedCurve p.symm.toContinuousMap q) := by
    intro t
    simp only [shiftedCurve, ContinuousMap.sub_apply, ContinuousMap.const_apply,
      Path.coe_toContinuousMap, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
    exact hL' (σ t)
  have hcl : p.symm.toContinuousMap 0 = p.symm.toContinuousMap 1 := by simp
  have hq' : ∀ t : I, p.symm.toContinuousMap t ≠ q := by
    intro t
    simp only [Path.coe_toContinuousMap]
    exact h (σ t)
  have hclp : p.toContinuousMap 0 = p.toContinuousMap 1 := by simp
  have hqp : ∀ t : I, p.toContinuousMap t ≠ q := by intro t; simpa using h t
  have hw := windingNumber_spec hcl hq' hLs
  have hwp := windingNumber_spec hclp hqp hL
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, unitInterval.symm_one,
    unitInterval.symm_zero] at hw
  have h2πi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have key : (2 * Real.pi * Complex.I) *
        ((windingNumber p.symm.toContinuousMap q : ℤ) : ℂ) =
      (2 * Real.pi * Complex.I) *
        (((-windingNumber p.toContinuousMap q : ℤ)) : ℂ) := by
    rw [Int.cast_neg, mul_neg, ← hwp, ← hw]
    ring
  exact_mod_cast mul_left_cancel₀ h2πi key

/-- **Winding stability**: a uniform perturbation smaller than the distance
to the base point does not change the winding number (divide the shifted
curves; the quotient stays in the disk about `1`, where a logarithm branch
lifts continuously). -/
theorem windingNumber_eq_of_dist_lt {γ₁ γ₂ : C(I, ℂ)} {q : ℂ}
    (hcl₁ : γ₁ 0 = γ₁ 1) (hcl₂ : γ₂ 0 = γ₂ 1)
    (h : ∀ t : I, ‖γ₂ t - γ₁ t‖ < ‖γ₁ t - q‖) :
    windingNumber γ₁ q = windingNumber γ₂ q := by
  have hne₁ : ∀ t : I, γ₁ t ≠ q := by
    intro t h'
    have h0 := h t
    rw [h', sub_self, norm_zero] at h0
    exact absurd h0 (not_lt.mpr (norm_nonneg _))
  have hne₁' : ∀ t : I, γ₁ t - q ≠ 0 := fun t => sub_ne_zero.mpr (hne₁ t)
  have hne₂ : ∀ t : I, γ₂ t ≠ q := by
    intro t h'
    have h0 := h t
    rw [h', norm_sub_rev] at h0
    exact lt_irrefl _ h0
  -- the quotient curve `(γ₂ - q)/(γ₁ - q)` stays in the disk about `1`
  have hcont_u : Continuous fun t : I => (γ₂ t - q) / (γ₁ t - q) :=
    (γ₂.continuous.sub continuous_const).div
      (γ₁.continuous.sub continuous_const) fun t => hne₁' t
  obtain ⟨u, hu_apply⟩ : ∃ u : C(I, ℂ), ∀ t : I,
      u t = (γ₂ t - q) / (γ₁ t - q) :=
    ⟨⟨fun t => (γ₂ t - q) / (γ₁ t - q), hcont_u⟩, fun t => rfl⟩
  have hu_near : ∀ t : I, ‖u t - 1‖ < 1 := by
    intro t
    have h1 : u t - 1 = (γ₂ t - γ₁ t) / (γ₁ t - q) := by
      rw [hu_apply t, div_sub_one (hne₁' t)]
      ring_nf
    rw [h1, norm_div]
    exact (div_lt_one (norm_pos_iff.mpr (hne₁' t))).mpr (h t)
  have hu_re : ∀ t : I, 0 < (u t).re := by
    intro t
    have h1 : |(u t).re - 1| ≤ ‖u t - 1‖ := by
      have h2 := Complex.abs_re_le_norm (u t - 1)
      simpa [Complex.sub_re, Complex.one_re] using h2
    have h3 := abs_lt.mp (lt_of_le_of_lt h1 (hu_near t))
    linarith [h3.1]
  have hu_ne : ∀ t : I, u t ≠ 0 := by
    intro t h'
    have h2 := hu_re t
    rw [h'] at h2
    simp at h2
  -- a continuous logarithm of the quotient
  have hcont_log : Continuous fun t : I => Complex.log (u t) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact ContinuousAt.clog u.continuous.continuousAt
      (Complex.mem_slitPlane_iff.mpr (Or.inl (hu_re t)))
  obtain ⟨Lu, hLu_apply⟩ : ∃ Lu : C(I, ℂ), ∀ t : I,
      Lu t = Complex.log (u t) :=
    ⟨⟨fun t => Complex.log (u t), hcont_log⟩, fun t => rfl⟩
  have hshift₁ : ∀ t : I, shiftedCurve γ₁ q t = γ₁ t - q := fun t => rfl
  have hshift₂ : ∀ t : I, shiftedCurve γ₂ q t = γ₂ t - q := fun t => rfl
  -- lift of the first shifted curve; add the quotient logarithm to lift
  -- the second
  obtain ⟨L₁, hL₁⟩ := exists_isLogLiftOf (shiftedCurve γ₁ q)
    (fun t => by rw [hshift₁ t]; exact hne₁' t)
  have hL₂ : IsLogLiftOf (L₁ + Lu) (shiftedCurve γ₂ q) := by
    intro t
    have happ : (L₁ + Lu) t = L₁ t + Lu t := rfl
    rw [happ, Complex.exp_add, hL₁ t, hLu_apply t,
      Complex.exp_log (hu_ne t), hshift₁ t, hshift₂ t, hu_apply t,
      mul_comm]
    exact div_mul_cancel₀ _ (hne₁' t)
  have hspec₁ := windingNumber_spec hcl₁ hne₁ hL₁
  have hspec₂ := windingNumber_spec hcl₂ hne₂ hL₂
  -- the quotient is a closed curve, so its logarithm has zero increment
  have hu01 : u 1 = u 0 := by
    rw [hu_apply 1, hu_apply 0, ← hcl₁, ← hcl₂]
  have hincr : (L₁ + Lu) 1 - (L₁ + Lu) 0 = L₁ 1 - L₁ 0 := by
    have e1 : (L₁ + Lu) 1 = L₁ 1 + Lu 1 := rfl
    have e0 : (L₁ + Lu) 0 = L₁ 0 + Lu 0 := rfl
    rw [e1, e0, hLu_apply 1, hLu_apply 0, hu01]
    ring
  rw [hspec₂, hspec₁] at hincr
  have hcast := mul_left_cancel₀ Complex.two_pi_I_ne_zero hincr
  exact_mod_cast hcast.symm

/-- The winding region of a closed curve — the set of base points off the
curve with nonzero winding — is open. -/
theorem isOpen_windingRegion {γ : C(I, ℂ)} (hcl : γ 0 = γ 1) :
    IsOpen {q : ℂ | q ∉ Set.range γ ∧ windingNumber γ q ≠ 0} := by
  rw [Metric.isOpen_iff]
  rintro q ⟨hq, hw⟩
  have hcomp : IsCompact (Set.range γ) := isCompact_range γ.continuous
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hcomp.isClosed.isOpen_compl q hq
  have key : ∀ y ∈ Metric.ball q r, windingNumber γ y = windingNumber γ q := by
    intro y hy
    have hyq : ‖y - q‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hy
    have hsegball : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
        q + (θ : ℂ) * (y - q) ∈ Metric.ball q r := by
      intro θ hθ
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul,
        Complex.norm_real, Real.norm_eq_abs]
      have habs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
      calc |θ| * ‖y - q‖ ≤ 1 * ‖y - q‖ :=
            mul_le_mul_of_nonneg_right habs (norm_nonneg _)
        _ = ‖y - q‖ := one_mul _
        _ < r := hyq
    have hC : IsPreconnected
        ((fun θ : ℝ => q + (θ : ℂ) * (y - q)) '' Set.Icc 0 1) :=
      isPreconnected_Icc.image _
        (continuous_const.add
          (Complex.continuous_ofReal.mul continuous_const)).continuousOn
    have hdisjC : ∀ t : I,
        γ t ∉ (fun θ : ℝ => q + (θ : ℂ) * (y - q)) '' Set.Icc 0 1 := by
      rintro t ⟨θ, hθ, ht⟩
      exact hball (by rw [← ht]; exact hsegball θ hθ) ⟨t, rfl⟩
    have hyC : y ∈ (fun θ : ℝ => q + (θ : ℂ) * (y - q)) '' Set.Icc 0 1 :=
      ⟨1, ⟨zero_le_one, le_refl 1⟩,
        by change q + ((1 : ℝ) : ℂ) * (y - q) = y; push_cast; ring⟩
    have hqC : q ∈ (fun θ : ℝ => q + (θ : ℂ) * (y - q)) '' Set.Icc 0 1 :=
      ⟨0, ⟨le_refl 0, zero_le_one⟩,
        by change q + ((0 : ℝ) : ℂ) * (y - q) = q; push_cast; ring⟩
    exact windingNumber_eq_of_preconnected hcl hC hdisjC hyC hqC
  exact ⟨r, hr, fun x hx => ⟨hball hx, fun h0 => hw ((key x hx).symm.trans h0)⟩⟩

/-- The winding region of a closed curve is bounded. -/
theorem isBounded_windingRegion {γ : C(I, ℂ)} (hcl : γ 0 = γ 1) :
    Bornology.IsBounded {q : ℂ | q ∉ Set.range γ ∧ windingNumber γ q ≠ 0} := by
  have hcomp : IsCompact (Set.range γ) := isCompact_range γ.continuous
  obtain ⟨R, hR⟩ := hcomp.isBounded.subset_closedBall 0
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R + 1)).subset ?_
  rintro q ⟨hq, hw⟩
  by_contra hqout
  refine hw (windingNumber_eq_zero_of_ball (c := 0) (r := R + 1) hcl ?_ ?_)
  · intro t
    have ht : γ t ∈ Metric.closedBall (0 : ℂ) R := hR (Set.mem_range_self t)
    rw [Metric.mem_closedBall] at ht
    rw [Metric.mem_ball]
    linarith
  · exact fun hb => hqout (Metric.ball_subset_closedBall hb)

/-- The frontier of the winding region lies on the curve: the winding number
is locally constant off the curve, so the region is relatively clopen in the
curve complement. -/
theorem frontier_windingRegion_subset {γ : C(I, ℂ)} (hcl : γ 0 = γ 1) :
    frontier {q : ℂ | q ∉ Set.range γ ∧ windingNumber γ q ≠ 0} ⊆
      Set.range γ := by
  intro x hx
  by_contra hxr
  have hcomp : IsCompact (Set.range γ) := isCompact_range γ.continuous
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hcomp.isClosed.isOpen_compl x hxr
  have key : ∀ y ∈ Metric.ball x r, windingNumber γ y = windingNumber γ x := by
    intro y hy
    have hyq : ‖y - x‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hy
    have hsegball : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
        x + (θ : ℂ) * (y - x) ∈ Metric.ball x r := by
      intro θ hθ
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul,
        Complex.norm_real, Real.norm_eq_abs]
      have habs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
      calc |θ| * ‖y - x‖ ≤ 1 * ‖y - x‖ :=
            mul_le_mul_of_nonneg_right habs (norm_nonneg _)
        _ = ‖y - x‖ := one_mul _
        _ < r := hyq
    have hC : IsPreconnected
        ((fun θ : ℝ => x + (θ : ℂ) * (y - x)) '' Set.Icc 0 1) :=
      isPreconnected_Icc.image _
        (continuous_const.add
          (Complex.continuous_ofReal.mul continuous_const)).continuousOn
    have hdisjC : ∀ t : I,
        γ t ∉ (fun θ : ℝ => x + (θ : ℂ) * (y - x)) '' Set.Icc 0 1 := by
      rintro t ⟨θ, hθ, ht⟩
      exact hball (by rw [← ht]; exact hsegball θ hθ) ⟨t, rfl⟩
    have hyC : y ∈ (fun θ : ℝ => x + (θ : ℂ) * (y - x)) '' Set.Icc 0 1 :=
      ⟨1, ⟨zero_le_one, le_refl 1⟩,
        by change x + ((1 : ℝ) : ℂ) * (y - x) = y; push_cast; ring⟩
    have hxC : x ∈ (fun θ : ℝ => x + (θ : ℂ) * (y - x)) '' Set.Icc 0 1 :=
      ⟨0, ⟨le_refl 0, zero_le_one⟩,
        by change x + ((0 : ℝ) : ℂ) * (y - x) = x; push_cast; ring⟩
    exact windingNumber_eq_of_preconnected hcl hC hdisjC hyC hxC
  rw [← closure_sdiff_interior] at hx
  obtain ⟨hxcl, hxni⟩ := hx
  by_cases hwx : windingNumber γ x = 0
  · obtain ⟨y, hyS, hyd⟩ := Metric.mem_closure_iff.mp hxcl r hr
    have hy : y ∈ Metric.ball x r := by rwa [Metric.mem_ball, dist_comm]
    exact hyS.2 ((key y hy).trans hwx)
  · have hsub : Metric.ball x r ⊆
        {q : ℂ | q ∉ Set.range γ ∧ windingNumber γ q ≠ 0} :=
      fun y hy => ⟨hball hy, fun h0 => hwx ((key y hy).symm.trans h0)⟩
    exact hxni (interior_maximal hsub Metric.isOpen_ball (Metric.mem_ball_self hr))

/-- **Polynomial argument principle, winding form.** For a nonzero
polynomial `p` and a closed curve avoiding its roots, the winding of the
image curve `p ∘ γ` about `0` is the sum over the root multiset of the
windings of `γ` about the roots: factor `p` into linear factors over `ℂ`
and apply multiplicativity. -/
theorem windingNumber_polynomial_comp (p : Polynomial ℂ) (hp : p ≠ 0)
    (γ : C(I, ℂ)) (hcl : γ 0 = γ 1)
    (hγ : ∀ t : I, p.eval (γ t) ≠ 0) :
    windingNumber ⟨fun t => p.eval (γ t),
        p.continuous.comp γ.continuous⟩ 0 =
      (p.roots.map fun ζ => windingNumber γ ζ).sum := by
  -- Pointwise evaluation of multiset products of shifted curves.
  have hprod_apply : ∀ (s : Multiset ℂ) (t : I),
      ((s.map fun ζ => shiftedCurve γ ζ).prod) t
        = (s.map fun ζ => γ t - ζ).prod := by
    intro s t
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, ContinuousMap.mul_apply, ih]
      congr 1
  -- Winding of the shifted curve about `0` is winding about the shift.
  have windKey : ∀ (δ : C(I, ℂ)) (ζ : ℂ),
      windingNumber (shiftedCurve δ ζ) 0 = windingNumber δ ζ := by
    intro δ ζ
    have h : shiftedCurve (shiftedCurve δ ζ) 0 = shiftedCurve δ ζ := by
      ext t
      simp [shiftedCurve]
    unfold windingNumber
    rw [h]
  -- Main induction over a root multiset avoided by the curve.
  have main : ∀ s : Multiset ℂ, (∀ t : I, ∀ ζ ∈ s, γ t ≠ ζ) →
      windingNumber ((s.map fun ζ => shiftedCurve γ ζ).prod) 0
        = (s.map fun ζ => windingNumber γ ζ).sum := by
    intro s
    induction s using Multiset.induction_on with
    | empty =>
      intro _
      simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.sum_zero]
      have h1 : (1 : C(I, ℂ)) = ContinuousMap.const I 1 := rfl
      rw [h1]
      exact windingNumber_const 1 0 one_ne_zero
    | cons a s ih =>
      intro hs
      have hγa : ∀ t : I, γ t ≠ a := fun t => hs t a (Multiset.mem_cons_self a s)
      have hcl₁ : (shiftedCurve γ a) 0 = (shiftedCurve γ a) 1 := by
        simp [shiftedCurve, hcl]
      have h₁ : ∀ t : I, (shiftedCurve γ a) t ≠ 0 := by
        intro t
        simp only [shiftedCurve, ContinuousMap.sub_apply, ContinuousMap.const_apply]
        exact sub_ne_zero_of_ne (hγa t)
      have hcl₂ : ((s.map fun ζ => shiftedCurve γ ζ).prod) 0
          = ((s.map fun ζ => shiftedCurve γ ζ).prod) 1 := by
        rw [hprod_apply s 0, hprod_apply s 1]
        simp only [hcl]
      have h₂ : ∀ t : I, ((s.map fun ζ => shiftedCurve γ ζ).prod) t ≠ 0 := by
        intro t
        rw [hprod_apply s t]
        refine Multiset.prod_ne_zero ?_
        intro h0
        obtain ⟨ζ, hζ, hζ0⟩ := Multiset.mem_map.mp h0
        exact hs t ζ (Multiset.mem_cons_of_mem hζ) (sub_eq_zero.mp hζ0)
      rw [Multiset.map_cons, Multiset.prod_cons,
        windingNumber_mul (shiftedCurve γ a)
          ((s.map fun ζ => shiftedCurve γ ζ).prod) hcl₁ hcl₂ h₁ h₂,
        windKey γ a, Multiset.map_cons, Multiset.sum_cons,
        ih (fun t ζ hζ => hs t ζ (Multiset.mem_cons_of_mem hζ))]
  -- Factor `p` as the product of its linear factors times a rootless cofactor.
  obtain ⟨q, hq⟩ := Polynomial.prod_multiset_X_sub_C_dvd p
  have hne : (Multiset.map (fun a => Polynomial.X - Polynomial.C a) p.roots).prod * q ≠ 0 := by
    rw [← hq]
    exact hp
  have hq0 : q ≠ 0 := by
    intro h
    apply hp
    rw [hq, h, mul_zero]
  have hqroots : q.roots = 0 := by
    have h1 : p.roots = p.roots + q.roots := by
      conv_lhs => rw [hq]
      rw [Polynomial.roots_mul hne, Polynomial.roots_multiset_prod_X_sub_C]
    have h2 : p.roots + q.roots = p.roots + 0 := by
      rw [add_zero]
      exact h1.symm
    exact add_left_cancel h2
  have hqne : ∀ z : ℂ, q.eval z ≠ 0 := by
    intro z h0
    have hz : z ∈ q.roots := Polynomial.mem_roots'.mpr ⟨hq0, h0⟩
    rw [hqroots] at hz
    simp at hz
  -- Pointwise factorization of the evaluated polynomial.
  have hev : ∀ z : ℂ, p.eval z
      = (p.roots.map fun ζ => z - ζ).prod * q.eval z := by
    intro z
    conv_lhs => rw [hq]
    rw [Polynomial.eval_mul, Polynomial.eval_multiset_prod, Multiset.map_map]
    simp
  -- The curve avoids every root of `p`.
  have hroots : ∀ t : I, ∀ ζ ∈ p.roots, γ t ≠ ζ := by
    intro t ζ hζ h
    apply hγ t
    rw [h]
    exact Polynomial.isRoot_of_mem_roots hζ
  -- Closedness and nonvanishing of the two factors.
  have hclprod : ((p.roots.map fun ζ => shiftedCurve γ ζ).prod) 0
      = ((p.roots.map fun ζ => shiftedCurve γ ζ).prod) 1 := by
    rw [hprod_apply p.roots 0, hprod_apply p.roots 1]
    simp only [hcl]
  have hprodne : ∀ t : I, ((p.roots.map fun ζ => shiftedCurve γ ζ).prod) t ≠ 0 := by
    intro t
    rw [hprod_apply p.roots t]
    refine Multiset.prod_ne_zero ?_
    intro h0
    obtain ⟨ζ, hζ, hζ0⟩ := Multiset.mem_map.mp h0
    exact hroots t ζ hζ (sub_eq_zero.mp hζ0)
  have hclq : (⟨fun t => q.eval (γ t), q.continuous.comp γ.continuous⟩ : C(I, ℂ)) 0
      = (⟨fun t => q.eval (γ t), q.continuous.comp γ.continuous⟩ : C(I, ℂ)) 1 := by
    simp only [ContinuousMap.coe_mk]
    rw [hcl]
  have hqne' : ∀ t : I,
      (⟨fun t => q.eval (γ t), q.continuous.comp γ.continuous⟩ : C(I, ℂ)) t ≠ 0 := by
    intro t
    simp only [ContinuousMap.coe_mk]
    exact hqne (γ t)
  -- The image curve as the pointwise product of the two factors.
  have hbundle : (⟨fun t => p.eval (γ t),
        p.continuous.comp γ.continuous⟩ : C(I, ℂ))
      = (p.roots.map fun ζ => shiftedCurve γ ζ).prod *
          ⟨fun t => q.eval (γ t), q.continuous.comp γ.continuous⟩ := by
    ext t
    simp only [ContinuousMap.coe_mk, ContinuousMap.mul_apply, hprod_apply p.roots t]
    exact hev (γ t)
  -- The rootless cofactor contributes zero winding: contract the curve
  -- through the straight-line homotopy and evaluate.
  have hqwind : windingNumber
      (⟨fun t => q.eval (γ t), q.continuous.comp γ.continuous⟩ : C(I, ℂ)) 0 = 0 := by
    have hcoe : Continuous fun x : I × I => ((x.1 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
    have hg : Continuous fun x : I × I =>
        (1 - ((x.1 : ℝ) : ℂ)) * γ x.2 + ((x.1 : ℝ) : ℂ) * γ 0 :=
      ((continuous_const.sub hcoe).mul (γ.continuous.comp continuous_snd)).add
        (hcoe.mul continuous_const)
    let H : ContinuousMap.HomotopyRel
        (⟨fun t => q.eval (γ t), q.continuous.comp γ.continuous⟩ : C(I, ℂ))
        (ContinuousMap.const I (q.eval (γ 0))) {0, 1} :=
      { toFun := fun x =>
          q.eval ((1 - ((x.1 : ℝ) : ℂ)) * γ x.2 + ((x.1 : ℝ) : ℂ) * γ 0)
        continuous_toFun := q.continuous.comp hg
        map_zero_left := by
          intro x
          simp
        map_one_left := by
          intro x
          simp
        prop' := by
          intro tt x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl
          · simp only [ContinuousMap.coe_mk]
            congr 1
            ring
          · simp only [ContinuousMap.coe_mk]
            rw [← hcl]
            congr 1
            ring }
    have hH : ∀ (t s : I), H (t, s) ≠ (0 : ℂ) := by
      intro t s
      change q.eval _ ≠ 0
      exact hqne _
    rw [windingNumber_eq_of_homotopicRel hclq H hH]
    exact windingNumber_const _ 0 (hqne (γ 0))
  rw [hbundle,
    windingNumber_mul ((p.roots.map fun ζ => shiftedCurve γ ζ).prod)
      (⟨fun t => q.eval (γ t), q.continuous.comp γ.continuous⟩)
      hclprod hclq hprodne hqne',
    main p.roots hroots, hqwind, add_zero]

end RiemannDynamics
