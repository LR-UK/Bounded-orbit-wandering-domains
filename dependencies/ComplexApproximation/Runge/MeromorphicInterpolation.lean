import Runge.Interpolation
import FunctionTheory.Meromorphic.CompactDecomposition

open Set Filter Polynomial FunctionTheory
open scoped Topology

namespace Runge

set_option autoImplicit false

private theorem polynomial_analyticAt (p : ℂ[X]) (a : ℂ) :
    AnalyticAt ℂ (fun z => p.eval z) a :=
  AnalyticOnNhd.eval_polynomial p a (mem_univ a)

/-- Meromorphic Runge approximation with unchanged principal parts and finite
jet interpolation at regular marked points. The analytic error is defined even
at the poles; its punctured-neighbourhood identity expresses cancellation of
all principal parts. New denominator zeros are confined to the allowed set. -/
theorem meromorphic_prescribed_poles_approximation_with_interpolation
    (K : Set ℂ) (hK : IsCompact K)
    (P : Set ℂ) (hP : MeetsBoundedComplementComponents K P)
    (f : ℂ → ℂ) (hf : MeromorphicOn f K)
    (s : Finset ℂ) (hsK : ∀ a ∈ s, a ∈ K)
    (hsreg : ∀ a ∈ s, AnalyticAt ℂ f a) (m : ℂ → ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (p q : ℂ[X]) (e : ℂ → ℂ), q ≠ 0 ∧
      (∀ a, q.eval a = 0 → (a ∈ K ∧ ¬ AnalyticAt ℂ f a) ∨ a ∈ P) ∧
      (∀ a ∈ K, AnalyticAt ℂ f a → q.eval a ≠ 0) ∧
      AnalyticOnNhd ℂ e K ∧
      (∀ a ∈ K, ‖e a‖ < ε) ∧
      (∀ a ∈ K, AnalyticAt ℂ f a → ‖f a - p.eval a / q.eval a‖ < ε) ∧
      (∀ a ∈ K, (fun z => f z - p.eval z / q.eval z) =ᶠ[𝓝[≠] a] e) ∧
      ∀ a ∈ s, ∀ k < m a,
        iteratedDeriv k f a = iteratedDeriv k (fun z => p.eval z / q.eval z) a := by
  obtain ⟨p₀, q₀, g, hq₀, hq₀sing, hg, hfg⟩ :=
    exists_rational_analytic_remainder hK hf
  let U : Set ℂ := {z | AnalyticAt ℂ g z}
  have hU : IsOpen U := isOpen_analyticAt ℂ g
  have hKU : K ⊆ U := hg
  have hgU : DifferentiableOn ℂ g U := fun z hz => hz.differentiableAt.differentiableWithinAt
  obtain ⟨r, q₁, hq₁, hq₁K, hq₁P, herr, hjet⟩ :=
    prescribed_poles_approximation_with_interpolation K hK P hP U hU hKU
      g hgU s hsK m ε hε
  let p := p₀ * q₁ + q₀ * r
  let q := q₀ * q₁
  let e := fun z => g z - r.eval z / q₁.eval z
  have hqreg (a : ℂ) (ha : AnalyticAt ℂ f a) : q₀.eval a ≠ 0 := by
    intro hz
    exact (hq₀sing a hz).2 ha
  have hidentity (z : ℂ) (h₀ : q₀.eval z ≠ 0) (h₁ : q₁.eval z ≠ 0) :
      f z - p.eval z / q.eval z = e z := by
    rw [hfg z h₀]
    dsimp [p, q, e]
    simp only [eval_add, eval_mul]
    field_simp
    ring
  refine ⟨p, q, e, mul_ne_zero hq₀ hq₁, ?_, ?_, ?_, herr, ?_, ?_, ?_⟩
  · intro a ha
    change (q₀ * q₁).eval a = 0 at ha
    rw [eval_mul, mul_eq_zero] at ha
    exact ha.elim (fun h => Or.inl (hq₀sing a h)) (fun h => Or.inr (hq₁P a h))
  · intro a ha hfa
    simpa only [q, eval_mul] using mul_ne_zero (hqreg a hfa) (hq₁K a ha)
  · intro a ha
    exact (hg a ha).sub ((polynomial_analyticAt r a).div
      (polynomial_analyticAt q₁ a) (hq₁K a ha))
  · intro a ha hfa
    rw [hidentity a (hqreg a hfa) (hq₁K a ha)]
    exact herr a ha
  · intro a _
    have h₀ : ∀ᶠ z in 𝓝[≠] a, q₀.eval z ≠ 0 :=
      (Polynomial.eventually_eval_ne_zero_cofinite hq₀).filter_mono (nhdsNE_le_cofinite a)
    have h₁ : ∀ᶠ z in 𝓝[≠] a, q₁.eval z ≠ 0 :=
      (Polynomial.eventually_eval_ne_zero_cofinite hq₁).filter_mono (nhdsNE_le_cofinite a)
    filter_upwards [h₀, h₁] with z hz₀ hz₁ using hidentity z hz₀ hz₁
  · intro a ha k hk
    have h₀ := hqreg a (hsreg a ha)
    have h₁ := hq₁K a (hsK a ha)
    have hlocal : (fun z => f z - p.eval z / q.eval z) =ᶠ[𝓝 a] e := by
      filter_upwards [q₀.continuous.continuousAt.eventually_ne h₀,
        q₁.continuous.continuousAt.eventually_ne h₁] with z hz₀ hz₁
      exact hidentity z hz₀ hz₁
    have hd := hlocal.iteratedDeriv_eq k
    have hR : AnalyticAt ℂ (fun z => p.eval z / q.eval z) a :=
      (polynomial_analyticAt p a).div (polynomial_analyticAt q a)
        (by simpa only [q, eval_mul] using mul_ne_zero h₀ h₁)
    rw [iteratedDeriv_fun_sub (hsreg a ha).contDiffAt hR.contDiffAt] at hd
    have hr : AnalyticAt ℂ (fun z => r.eval z / q₁.eval z) a :=
      (polynomial_analyticAt r a).div (polynomial_analyticAt q₁ a) h₁
    have hezero : iteratedDeriv k e a = 0 := by
      dsimp only [e]
      rw [iteratedDeriv_fun_sub (hg a (hsK a ha)).contDiffAt
        hr.contDiffAt,
        hjet a ha k hk, sub_self]
    rw [hezero] at hd
    exact sub_eq_zero.mp hd

end Runge
