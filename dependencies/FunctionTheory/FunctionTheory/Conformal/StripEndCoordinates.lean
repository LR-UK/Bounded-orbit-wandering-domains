import FunctionTheory.Conformal.StripEndAsymptotics
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! # Recovering a strip map from its exponential coordinate

The exponential identity and the choice of logarithm branch are explicit.
These lemmas turn an analytic simple-zero extension into estimates for the
original map itself. Establishing that extension for a geometric domain is
a separate step.
-/

open Set Filter Asymptotics Complex
open scoped Topology

namespace FunctionTheory

theorem deriv_eq_logDeriv_of_exp_identity {U : Set ℂ} {φ ψ : ℂ → ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    (heq : EqOn (fun z => ψ (exp (-z))) (fun z => exp (-φ z)) U)
    {z : ℂ} (hz : z ∈ U) (hψ : DifferentiableAt ℂ ψ (exp (-z))) :
    deriv φ z = exp (-z) * deriv ψ (exp (-z)) / ψ (exp (-z)) := by
  have hdφ := (hφ z hz).differentiableAt (hU.mem_nhds hz)
  have hleft := hψ.hasDerivAt.comp z ((hasDerivAt_id z).neg.cexp)
  have hright := hdφ.hasDerivAt.neg.cexp
  have hpoint : ψ (exp (-z)) = exp (-φ z) := heq hz
  have hlocal : (fun w => ψ (exp (-w))) =ᶠ[𝓝 z] (fun w => exp (-φ w)) :=
    Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => heq hw
  have hd : deriv ψ (exp (-z)) * (exp (-z) * (-1)) =
      exp (-φ z) * (-deriv φ z) := by
    exact hleft.unique (hright.congr_of_eventuallyEq hlocal)
  have hne : ψ (exp (-z)) ≠ 0 := by rw [hpoint]; exact exp_ne_zero _
  apply (eq_div_iff hne).mpr
  rw [hpoint]
  linear_combination hd

theorem stripEnd_derivative_estimate_of_exp_identity {U : Set ℂ} {φ ψ : ℂ → ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    (heq : EqOn (fun z => ψ (exp (-z))) (fun z => exp (-φ z)) U)
    (hψ : AnalyticAt ℂ ψ 0) (hψ0 : ψ 0 = 0) (hdψ : deriv ψ 0 ≠ 0) :
    (fun z => deriv φ z - 1) =O[comap Complex.re atTop ⊓ 𝓟 U]
      (fun z => Real.exp (-z.re)) := by
  have ha : ∀ᶠ z in comap Complex.re atTop, AnalyticAt ℂ ψ (exp (-z)) :=
    tendsto_exp_neg_re_atTop.mono_right nhdsWithin_le_nhds |>.eventually hψ.eventually_analyticAt
  apply ((stripEnd_logDeriv_estimate hψ hψ0 hdψ).mono inf_le_left).congr' _ .rfl
  filter_upwards [ha.filter_mono inf_le_left,
    show ∀ᶠ z in comap Complex.re atTop ⊓ 𝓟 U, z ∈ U from
      Filter.Eventually.filter_mono inf_le_right (Filter.eventually_principal.mpr (fun _ h => h))]
      with z hzψ hzU
  rw [deriv_eq_logDeriv_of_exp_identity hU hφ heq hzU hzψ.differentiableAt]

theorem sub_eq_neg_log_quotient_of_exp_identity {φ ψ : ℂ → ℂ} {z : ℂ}
    (heq : ψ (exp (-z)) = exp (-φ z))
    (hlo : -Real.pi < (z - φ z).im) (hhi : (z - φ z).im ≤ Real.pi) :
    φ z - z = -log (ψ (exp (-z)) / exp (-z)) := by
  have hquot : ψ (exp (-z)) / exp (-z) = exp (z - φ z) := by
    rw [heq, ← exp_sub]
    congr 1
    ring
  rw [hquot, log_exp hlo hhi]
  ring

theorem stripEnd_value_estimate_of_exp_identity {U : Set ℂ} {φ ψ : ℂ → ℂ}
    (heq : EqOn (fun z => ψ (exp (-z))) (fun z => exp (-φ z)) U)
    (hbranch : ∀ z ∈ U, -Real.pi < (z - φ z).im ∧ (z - φ z).im ≤ Real.pi)
    (hψ : AnalyticAt ℂ ψ 0) (hψ0 : ψ 0 = 0) (hdψ : deriv ψ 0 ∈ slitPlane) :
    (fun z => φ z - z + log (deriv ψ 0)) =O[comap Complex.re atTop ⊓ 𝓟 U]
      (fun z => Real.exp (-z.re)) := by
  apply ((stripEnd_log_quotient_estimate hψ hψ0 hdψ).mono inf_le_left).neg_left.congr' _ .rfl
  filter_upwards [show ∀ᶠ z in comap Complex.re atTop ⊓ 𝓟 U, z ∈ U from
    Filter.Eventually.filter_mono inf_le_right (Filter.eventually_principal.mpr (fun _ h => h))]
    with z hz
  rw [sub_eq_neg_log_quotient_of_exp_identity (heq hz) (hbranch z hz).1 (hbranch z hz).2]
  ring

/-- The two asymptotics in Lemma 7.2, once the geometric argument has supplied
the analytic extension with positive real derivative at zero. The source and
image strip bounds identify the principal logarithm branch. -/
theorem stripEnd_estimates_of_reflected_map {U : Set ℂ} {φ ψ : ℂ → ℂ} {a : ℝ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    (heq : EqOn (fun z => ψ (exp (-z))) (fun z => exp (-φ z)) U)
    (hsource : ∀ z ∈ U, |z.im| < Real.pi / 2)
    (htarget : ∀ z ∈ U, |(φ z).im| < Real.pi / 2)
    (hψ : AnalyticAt ℂ ψ 0) (hψ0 : ψ 0 = 0)
    (ha : 0 < a) (hdψ : deriv ψ 0 = (a : ℂ)) :
    ∃ ρ : ℝ,
      (fun z => deriv φ z - 1) =O[comap Complex.re atTop ⊓ 𝓟 U]
        (fun z => Real.exp (-z.re)) ∧
      (fun z => φ z - (z + (ρ : ℂ))) =O[comap Complex.re atTop ⊓ 𝓟 U]
        (fun z => Real.exp (-z.re)) := by
  have hne : deriv ψ 0 ≠ 0 := by
    rw [hdψ]
    exact Complex.ofReal_ne_zero.mpr ha.ne'
  have hslit : deriv ψ 0 ∈ slitPlane := by
    rw [hdψ]
    exact Complex.ofReal_mem_slitPlane.mpr ha
  have hbranch : ∀ z ∈ U, -Real.pi < (z - φ z).im ∧ (z - φ z).im ≤ Real.pi := by
    intro z hz
    obtain ⟨hzlo, hzhi⟩ := abs_lt.mp (hsource z hz)
    obtain ⟨hφlo, hφhi⟩ := abs_lt.mp (htarget z hz)
    simp only [Complex.sub_im]
    constructor <;> linarith
  have hval := stripEnd_value_estimate_of_exp_identity heq hbranch hψ hψ0 hslit
  have hlog : log (deriv ψ 0) = (Real.log a : ℂ) := by
    rw [hdψ, ← Complex.ofReal_log ha.le]
  refine ⟨-Real.log a, stripEnd_derivative_estimate_of_exp_identity hU hφ heq hψ hψ0 hne, ?_⟩
  apply hval.congr' (.of_forall ?_) .rfl
  intro z
  rw [hlog]
  push_cast
  ring

end FunctionTheory
