/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.OldPunctureBoundaryMass
import BoundedWanderingDomains.Surfaces.PunctureBoundaryMass
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Finite assembly of puncture boundary masses

The local end estimates used in the surface Riesz argument are naturally
indexed by the finitely many old and new punctures of a compactification.
This file packages the elementary finite-sum step: old-end terms vanish,
while finitely many uniformly bounded new-end terms have a finite total
bound. -/

open Set Function Filter
open MeasureTheory
open scoped Topology ENNReal

namespace AreaDeficit.Surfaces

/-- A finite sum of terms which tend to zero also tends to zero. -/
theorem tendsto_finset_sum_zero {ι : Type*} (s : Finset ι)
    (u : ι → ℝ → ℝ)
    (hu : ∀ i ∈ s, Tendsto (u i) atTop (𝓝 0)) :
    Tendsto (fun t => ∑ i ∈ s, u i t) atTop (𝓝 0) := by
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum s (fun i hi => hu i hi)

/-- Pointwise eventual bounds add over a finite family. -/
theorem eventually_abs_finset_sum_le {ι : Type*} (s : Finset ι)
    (u : ι → ℝ → ℝ) (B : ι → ℝ)
    (hu : ∀ i ∈ s, ∀ᶠ t in atTop, |u i t| ≤ B i) :
    ∀ᶠ t in atTop, |∑ i ∈ s, u i t| ≤ ∑ i ∈ s, B i := by
  filter_upwards [(eventually_all_finset s).mpr hu] with t ht
  exact (Finset.abs_sum_le_sum_abs (fun j => u j t) s).trans
    (Finset.sum_le_sum fun j hj => ht j hj)

/-- The sum of vanishing old-end terms and bounded new-end terms has one
finite eventual bound.  The extra `1` absorbs the old-end sum after it has
become small. -/
theorem eventually_bounded_old_new_boundary_sum
    {ι κ : Type*} (old : Finset ι) (new : Finset κ)
    (u : ι → ℝ → ℝ) (v : κ → ℝ → ℝ) (B : κ → ℝ)
    (hu : ∀ i ∈ old, Tendsto (u i) atTop (𝓝 0))
    (hv : ∀ j ∈ new, ∀ᶠ t in atTop, |v j t| ≤ B j) :
    ∀ᶠ t in atTop,
      |(∑ i ∈ old, u i t) + ∑ j ∈ new, v j t| ≤
        1 + ∑ j ∈ new, B j := by
  have hold : Tendsto (fun t => ∑ i ∈ old, u i t) atTop (𝓝 0) :=
    tendsto_finset_sum_zero old u hu
  have holdBound : ∀ᶠ t in atTop, |∑ i ∈ old, u i t| ≤ 1 := by
    have h := hold.eventually (Metric.closedBall_mem_nhds 0 zero_lt_one)
    filter_upwards [h] with t ht
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using ht
  have hnew := eventually_abs_finset_sum_le new v B hv
  filter_upwards [holdBound, hnew] with t htold htnew
  exact (abs_add_le _ _).trans <| by linarith

/-- Uniform bounds for an exhausting family of nonnegative cutoff integrals
bound the total mass.  This is the measure-theoretic endpoint of the global
Riesz assembly and avoids subtracting two possibly infinite areas. -/
theorem measure_univ_le_of_cutoff_lintegrals
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (χ : ℕ → α → ℝ≥0∞) (hχ : ∀ n, AEMeasurable (χ n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => χ n x) atTop (𝓝 1))
    {C : ℝ≥0∞} (hbound : ∀ n, ∫⁻ x, χ n x ∂μ ≤ C) :
    μ Set.univ ≤ C := by
  rw [← lintegral_one]
  calc
    (∫⁻ _x : α, (1 : ℝ≥0∞) ∂μ) =
        ∫⁻ x : α, liminf (fun n => χ n x) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hlim] with x hx
      exact hx.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x, χ n x ∂μ) atTop :=
      lintegral_liminf_le' hχ
    _ ≤ C := by
      have hb : ∀ᶠ n : ℕ in atTop, (∫⁻ x, χ n x ∂μ) ≤ C :=
        Filter.Eventually.of_forall hbound
      have h := Filter.liminf_le_liminf hb
      simpa only [liminf_const] using h

/-- Riesz-cutoff form of `measure_univ_le_of_cutoff_lintegrals`.  If every
cutoff mass is the nonnegative real boundary pairing and those pairings are
eventually bounded in absolute value, the whole Riesz measure has finite
mass.  Passing to a tail removes the word `eventually` without changing the
exhaustion. -/
theorem measure_univ_le_of_eventually_bounded_riesz_cutoffs
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (χ : ℕ → α → ℝ≥0∞) (hχ : ∀ n, AEMeasurable (χ n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => χ n x) atTop (𝓝 1))
    (boundary : ℕ → ℝ)
    (hgreen : ∀ n, (∫⁻ x, χ n x ∂μ) = ENNReal.ofReal (boundary n))
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᶠ n : ℕ in atTop, |boundary n| ≤ B) :
    μ Set.univ ≤ ENNReal.ofReal B := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  let ψ : ℕ → α → ℝ≥0∞ := fun n => χ (n + N)
  apply measure_univ_le_of_cutoff_lintegrals μ ψ
  · intro n
    exact hχ (n + N)
  · filter_upwards [hlim] with x hx
    exact hx.comp (tendsto_add_atTop_nat N)
  · intro n
    rw [show (∫⁻ x, ψ n x ∂μ) = ENNReal.ofReal (boundary (n + N)) by
      simpa only [ψ] using hgreen (n + N)]
    apply ENNReal.ofReal_le_ofReal
    exact (le_abs_self (boundary (n + N))).trans (hN _ (Nat.le_add_left N n))

end AreaDeficit.Surfaces

#print axioms AreaDeficit.Surfaces.tendsto_finset_sum_zero
#print axioms AreaDeficit.Surfaces.eventually_abs_finset_sum_le
#print axioms AreaDeficit.Surfaces.eventually_bounded_old_new_boundary_sum
#print axioms AreaDeficit.Surfaces.measure_univ_le_of_cutoff_lintegrals
#print axioms AreaDeficit.Surfaces.measure_univ_le_of_eventually_bounded_riesz_cutoffs
