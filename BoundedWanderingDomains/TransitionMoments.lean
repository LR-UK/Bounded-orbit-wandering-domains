/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.Regularisation
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace AreaDeficit

noncomputable def transitionSecond : ℝ → ℝ := deriv (deriv Real.smoothTransition)

theorem transition_deriv_contDiff : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
  (Real.smoothTransition.contDiff : ContDiff ℝ (∞ + 1) Real.smoothTransition).deriv'

theorem transitionSecond_contDiff : ContDiff ℝ ∞ transitionSecond :=
  (transition_deriv_contDiff : ContDiff ℝ (∞ + 1) (deriv Real.smoothTransition)).deriv'

theorem transition_deriv_hasDerivAt (t : ℝ) :
    HasDerivAt (deriv Real.smoothTransition) (transitionSecond t) t :=
  (transition_deriv_contDiff.differentiable (by simp) t).hasDerivAt

theorem transition_deriv_eq_zero_left {t : ℝ} (ht : t ≤ 0) :
    deriv Real.smoothTransition t = 0 := by
  apply IsLocalMin.deriv_eq_zero
  exact Filter.Eventually.of_forall (fun y => by
    rw [Real.smoothTransition.zero_of_nonpos ht]
    exact Real.smoothTransition.nonneg y)

theorem transition_deriv_eq_zero_right {t : ℝ} (ht : 1 ≤ t) :
    deriv Real.smoothTransition t = 0 := by
  apply IsLocalMax.deriv_eq_zero
  exact Filter.Eventually.of_forall (fun y => by
    rw [Real.smoothTransition.one_of_one_le ht]
    exact Real.smoothTransition.le_one y)

theorem transitionSecond_eq_zero {t : ℝ} (ht : t ≤ 0 ∨ 1 ≤ t) :
    transitionSecond t = 0 := by
  have he : deriv Real.smoothTransition t = 0 := ht.elim
    transition_deriv_eq_zero_left transition_deriv_eq_zero_right
  apply IsLocalMin.deriv_eq_zero
  exact Filter.Eventually.of_forall (fun y => by
    rw [he]
    exact transition_deriv_nonneg y)

theorem transitionSecond_tsupport : tsupport transitionSecond ⊆ Icc (0 : ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hn
  simp only [mem_Icc, not_and_or, not_le] at hn
  exact ht (transitionSecond_eq_zero (hn.imp le_of_lt le_of_lt))

theorem transitionSecond_integrable : Integrable transitionSecond :=
  transitionSecond_contDiff.continuous.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) transitionSecond_tsupport)

/-- The second derivative has zero mass. -/
theorem integral_transitionSecond : (∫ t in (0 : ℝ)..1, transitionSecond t) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => transition_deriv_hasDerivAt t)
    (transitionSecond_contDiff.continuous.intervalIntegrable 0 1),
    transition_deriv_eq_zero_right le_rfl, transition_deriv_eq_zero_left le_rfl, sub_self]

/-- Its first moment is minus one; this is the end contribution in the area formula. -/
theorem integral_mul_transitionSecond :
    (∫ t in (0 : ℝ)..1, t * transitionSecond t) = -1 := by
  have hd (t : ℝ) : HasDerivAt
      (fun s => s * deriv Real.smoothTransition s - Real.smoothTransition s)
      (t * transitionSecond t) t := by
    simpa only [Pi.mul_def, Pi.sub_def, id_eq, one_mul, add_sub_cancel_left] using
      ((hasDerivAt_id t).mul (transition_deriv_hasDerivAt t)).sub
        (transition_hasDerivAt t)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((continuous_id.mul transitionSecond_contDiff.continuous).intervalIntegrable 0 1)]
  simp [transition_deriv_eq_zero_right le_rfl]

end AreaDeficit
