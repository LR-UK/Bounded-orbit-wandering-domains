import ComplexApproximation.CauchyPompeiu

/-!
# Uniform estimates for the Cauchy transform

Splitting the kernel into its part on the unit disk and its bounded remainder
gives an estimate uniform in the evaluation point. This is the estimate needed
for the correction terms in the Rosay–Rudin approximation argument.
-/

open Complex MeasureTheory Set Function Metric
open scoped Topology ContDiff

namespace ComplexApproximation

noncomputable def cauchyKernelMass : ℝ :=
  ∫ w : ℂ in closedBall 0 1, ‖w⁻¹‖

theorem cauchyKernelMass_nonneg : 0 ≤ cauchyKernelMass :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem norm_cauchyTransform_le {q : ℂ → ℂ} (hq : Continuous q)
    (hc : HasCompactSupport q) {M : ℝ}
    (hbound : ∀ w, ‖q w‖ ≤ M) (z : ℂ) :
    ‖cauchyTransform q z‖ ≤ M * cauchyKernelMass + ∫ w : ℂ, ‖q w‖ := by
  let k : ℂ → ℝ := (closedBall 0 1).indicator (fun w : ℂ => ‖w⁻¹‖)
  have hk : Integrable k := by
    rw [integrable_indicator_iff isClosed_closedBall.measurableSet]
    exact (locallyIntegrable_cauchyKernel.integrableOn_isCompact
      (isCompact_closedBall 0 1)).norm
  have hqi : Integrable (fun w : ℂ => ‖q w‖) :=
    (hq.integrable_of_hasCompactSupport hc).norm
  have hqz : Integrable (fun w : ℂ => ‖q (z - w)‖) := hqi.comp_sub_left z
  have hmajor (w : ℂ) : ‖w⁻¹ * q (z - w)‖ ≤ M * k w + ‖q (z - w)‖ := by
    by_cases hw : w ∈ closedBall (0 : ℂ) 1
    · simp only [k, indicator_of_mem hw, norm_mul]
      calc
        ‖w⁻¹‖ * ‖q (z - w)‖ ≤ ‖w⁻¹‖ * M :=
          mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
        _ ≤ M * ‖w⁻¹‖ + ‖q (z - w)‖ := by
          rw [mul_comm]
          exact le_add_of_nonneg_right (norm_nonneg _)
    · have hw1 : 1 < ‖w‖ := by simpa only [mem_closedBall_zero_iff, not_le] using hw
      have hinv : ‖w⁻¹‖ ≤ 1 := by
        rw [norm_inv]
        exact inv_le_one_of_one_le₀ hw1.le
      simp only [k, indicator_of_notMem hw, mul_zero, zero_add, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hinv
  calc
    ‖cauchyTransform q z‖ ≤ ∫ w : ℂ, ‖w⁻¹ * q (z - w)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ w : ℂ, M * k w + ‖q (z - w)‖ :=
      integral_mono (integrable_cauchyTransform_integrand hq hc z).norm
        ((hk.const_mul M).add hqz) hmajor
    _ = M * cauchyKernelMass + ∫ w : ℂ, ‖q w‖ := by
      rw [integral_add (hk.const_mul M) hqz, integral_const_mul,
        integral_sub_left_eq_self (fun w : ℂ => ‖q w‖) volume z]
      simp only [k, integral_indicator isClosed_closedBall.measurableSet, cauchyKernelMass]

theorem norm_cauchyTransform_le_of_support_subset {q : ℂ → ℂ} (hq : Continuous q)
    (hc : HasCompactSupport q) {K : Set ℂ} (hK : IsCompact K) (hsub : support q ⊆ K)
    {M : ℝ} (hbound : ∀ w, ‖q w‖ ≤ M) (z : ℂ) :
    ‖cauchyTransform q z‖ ≤ M * (cauchyKernelMass + volume.real K) := by
  have hint : (∫ w : ℂ, ‖q w‖) ≤ M * volume.real K := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) (f := fun w => ‖q w‖)
      (fun w hw => by
        have hq0 : q w = 0 := by
          by_contra hn
          exact hw (hsub hn)
        simp [hq0])]
    calc
      (∫ w in K, ‖q w‖) ≤ ‖∫ w in K, ‖q w‖‖ := le_abs_self _
      _ ≤ M * volume.real K := norm_setIntegral_le_of_norm_le_const hK.measure_lt_top
        (fun w _ => by simpa only [norm_norm] using hbound w)
  calc
    ‖cauchyTransform q z‖ ≤ M * cauchyKernelMass + ∫ w : ℂ, ‖q w‖ :=
      norm_cauchyTransform_le hq hc hbound z
    _ ≤ M * (cauchyKernelMass + volume.real K) := by nlinarith

/-- A uniform bound for the solution operator, depending only on a fixed
compact set containing the support of the density. -/
theorem norm_solveCauchyRiemann_le {q : ℂ → ℂ} (hq : Continuous q)
    (hc : HasCompactSupport q) {K : Set ℂ} (hK : IsCompact K) (hsub : support q ⊆ K)
    {M : ℝ} (hbound : ∀ w, ‖q w‖ ≤ M) (z : ℂ) :
    ‖solveCauchyRiemann q z‖ ≤
      ‖(2 * Real.pi * I : ℂ)⁻¹‖ * (cauchyKernelMass + volume.real K) * M := by
  rw [solveCauchyRiemann, norm_mul]
  calc
    _ ≤ ‖(2 * Real.pi * I : ℂ)⁻¹‖ *
        (M * (cauchyKernelMass + volume.real K)) :=
      mul_le_mul_of_nonneg_left
        (norm_cauchyTransform_le_of_support_subset hq hc hK hsub hbound z) (norm_nonneg _)
    _ = _ := by ring

/-- The operator has a strictly positive uniform bound on densities supported
in any fixed compact set. -/
theorem exists_bound_solveCauchyRiemann (K : Set ℂ) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℂ → ℂ), Continuous q → HasCompactSupport q →
      support q ⊆ K → ∀ M : ℝ, 0 ≤ M → (∀ w, ‖q w‖ ≤ M) →
      ∀ z, ‖solveCauchyRiemann q z‖ ≤ C * M := by
  let C := ‖(2 * Real.pi * I : ℂ)⁻¹‖ * (cauchyKernelMass + volume.real K)
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _)
    (add_nonneg cauchyKernelMass_nonneg ENNReal.toReal_nonneg)
  refine ⟨C + 1, by positivity, ?_⟩
  intro q hq hc hsub M hM hb z
  exact (norm_solveCauchyRiemann_le hq hc hK hsub hb z).trans
    (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hM)

end ComplexApproximation
