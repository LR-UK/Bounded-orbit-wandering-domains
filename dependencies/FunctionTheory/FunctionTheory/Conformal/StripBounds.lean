import TauCeti.Analysis.Complex.Conformal.Inverse.Function
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Uniform derivative bounds on closed insets of decorated strips

A closed set bounded in imaginary direction and bounded to the left has
compact left truncations. Bounds on a right-hand tail therefore extend to
global bounds for a continuous nonvanishing function on the set.
-/

open Set Metric Bornology Filter Asymptotics
open scoped Topology

namespace FunctionTheory

theorem isCompact_left_truncation_of_strip_bounds {S : Set ℂ} {L M R : ℝ}
    (hS : IsClosed S) (hleft : ∀ z ∈ S, L ≤ z.re)
    (him : ∀ z ∈ S, |z.im| ≤ M) :
    IsCompact (S ∩ {z : ℂ | z.re ≤ R}) := by
  apply isCompact_iff_isClosed_bounded.mpr
  refine ⟨hS.inter (isClosed_le Complex.continuous_re continuous_const), ?_⟩
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨|L| + |R| + M, ?_⟩
  intro z hz
  have hre : |z.re| ≤ |L| + |R| := by
    apply abs_le.mpr
    have hl := hleft z hz.1
    have hr : z.re ≤ R := hz.2
    constructor <;> linarith [neg_abs_le L, le_abs_self R, abs_nonneg L, abs_nonneg R]
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add hre (him z hz.1))

theorem exists_norm_bounds_of_strip_tail {S : Set ℂ} {q : ℂ → ℂ} {L M R m B : ℝ}
    (hS : IsClosed S) (hleft : ∀ z ∈ S, L ≤ z.re) (him : ∀ z ∈ S, |z.im| ≤ M)
    (hq : ContinuousOn q S) (hne : ∀ z ∈ S, q z ≠ 0) (hm : 0 < m) (hB : 0 < B)
    (htail : ∀ z ∈ S, R ≤ z.re → m ≤ ‖q z‖ ∧ ‖q z‖ ≤ B) :
    ∃ m' B' : ℝ, 0 < m' ∧ 0 < B' ∧ ∀ z ∈ S, m' ≤ ‖q z‖ ∧ ‖q z‖ ≤ B' := by
  let K := S ∩ {z : ℂ | z.re ≤ R}
  have hK : IsCompact K := isCompact_left_truncation_of_strip_bounds hS hleft him
  rcases K.eq_empty_or_nonempty with hKe | hKn
  · refine ⟨m, B, hm, hB, ?_⟩
    intro z hz
    apply htail z hz
    by_contra h
    have hzK : z ∈ K := ⟨hz, (lt_of_not_ge h).le⟩
    simpa only [hKe, mem_empty_iff_false] using hzK
  · have hqn : ContinuousOn (fun z => ‖q z‖) K := hq.norm.mono inter_subset_left
    obtain ⟨u, hu, hmin⟩ := hK.exists_isMinOn hKn hqn
    obtain ⟨v, hv, hmax⟩ := hK.exists_isMaxOn hKn hqn
    refine ⟨min m ‖q u‖, max B ‖q v‖,
      lt_min hm (norm_pos_iff.mpr (hne u hu.1)), lt_of_lt_of_le hB (le_max_left _ _), ?_⟩
    intro z hz
    by_cases hr : z.re ≤ R
    · exact ⟨(min_le_right _ _).trans (hmin ⟨hz, hr⟩),
        (hmax ⟨hz, hr⟩).trans (le_max_right _ _)⟩
    · obtain ⟨hlo, hup⟩ := htail z hz (le_of_not_ge hr)
      exact ⟨(min_le_left _ _).trans hlo, hup.trans (le_max_left _ _)⟩

/-- Nonvanishing conformal derivatives on the compact part and convergence
to one on the right-hand tail give global two-sided derivative bounds. -/
theorem exists_derivative_bounds_of_strip_tail {U S : Set ℂ} {f : ℂ → ℂ} {L M R : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    (hS : IsClosed S) (hSU : S ⊆ U) (hleft : ∀ z ∈ S, L ≤ z.re)
    (him : ∀ z ∈ S, |z.im| ≤ M)
    (htail : ∀ z ∈ S, R ≤ z.re → ‖deriv f z - 1‖ < 1 / 2) :
    ∃ m B : ℝ, 0 < m ∧ 0 < B ∧ ∀ z ∈ S, m ≤ ‖deriv f z‖ ∧ ‖deriv f z‖ ≤ B := by
  apply exists_norm_bounds_of_strip_tail (R := R) (m := 1 / 2) (B := 3 / 2)
    hS hleft him ((hf.deriv hU).continuousOn.mono hSU)
    (fun z hz => TauCeti.deriv_ne_zero_of_injOn hf hU hinj (hSU hz)) (by norm_num) (by norm_num)
  intro z hz hr
  have h := htail z hz hr
  have hu := norm_add_le (deriv f z - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at hu
  have hl := norm_sub_le (deriv f z) (deriv f z - 1)
  rw [sub_sub_cancel, norm_one] at hl
  constructor <;> linarith

theorem exists_derivative_bounds_of_strip_limit {U S : Set ℂ} {f : ℂ → ℂ} {L M : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    (hS : IsClosed S) (hSU : S ⊆ U) (hleft : ∀ z ∈ S, L ≤ z.re)
    (him : ∀ z ∈ S, |z.im| ≤ M)
    (hlim : Tendsto (deriv f) (comap Complex.re atTop ⊓ 𝓟 S) (𝓝 1)) :
    ∃ m B : ℝ, 0 < m ∧ 0 < B ∧ ∀ z ∈ S, m ≤ ‖deriv f z‖ ∧ ‖deriv f z‖ ≤ B := by
  have hevent : ∀ᶠ z in comap Complex.re atTop ⊓ 𝓟 S,
      ‖deriv f z - 1‖ < 1 / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using
      hlim.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨R, hR⟩ := eventually_atTop.mp (eventually_comap.mp
    (eventually_inf_principal.mp hevent))
  exact exists_derivative_bounds_of_strip_tail hU hf hinj hS hSU hleft him
    (fun z hz hr => hR z.re hr z rfl hz)

/-- The exponential derivative asymptotic, once established geometrically,
implies exactly the uniform derivative bounds needed on a closed inset. -/
theorem exists_derivative_bounds_of_strip_asymptotic {U S : Set ℂ}
    {f : ℂ → ℂ} {L M : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    (hS : IsClosed S) (hSU : S ⊆ U) (hleft : ∀ z ∈ S, L ≤ z.re)
    (him : ∀ z ∈ S, |z.im| ≤ M)
    (hO : (fun z => deriv f z - 1) =O[comap Complex.re atTop ⊓ 𝓟 S]
      (fun z => Real.exp (-z.re))) :
    ∃ m B : ℝ, 0 < m ∧ 0 < B ∧ ∀ z ∈ S, m ≤ ‖deriv f z‖ ∧ ‖deriv f z‖ ≤ B := by
  have hdecay : Tendsto (fun z : ℂ => Real.exp (-z.re))
      (comap Complex.re atTop ⊓ 𝓟 S) (𝓝 0) := by
    apply Tendsto.mono_left _ inf_le_left
    simpa only [Function.comp_def] using
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (show Tendsto Complex.re (comap Complex.re atTop) atTop from tendsto_comap))
  exact exists_derivative_bounds_of_strip_limit hU hf hinj hS hSU hleft him
    (tendsto_sub_nhds_zero_iff.mp (hO.trans_tendsto hdecay))

end FunctionTheory
