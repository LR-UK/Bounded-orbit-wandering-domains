/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.OldPunctureBoundaryMass
import BoundedWanderingDomains.Surfaces.PunctureBoundaryMass

/-! # Finite assembly of puncture boundary masses

The local end estimates used in the surface Riesz argument are naturally
indexed by the finitely many old and new punctures of a compactification.
This file packages the elementary finite-sum step: old-end terms vanish,
while finitely many uniformly bounded new-end terms have a finite total
bound. -/

open Set Function Filter
open scoped Topology

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

end AreaDeficit.Surfaces

#print axioms AreaDeficit.Surfaces.tendsto_finset_sum_zero
#print axioms AreaDeficit.Surfaces.eventually_abs_finset_sum_le
#print axioms AreaDeficit.Surfaces.eventually_bounded_old_new_boundary_sum
