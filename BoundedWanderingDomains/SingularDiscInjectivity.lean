/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.SingularValues
import BoundedWanderingDomains.ChartDiscs

/-!
# Injectivity on intrinsic discs avoiding singular values

Once a successor intrinsic disc avoids the singular set, the global covering
property makes the map injective on the preceding disc.  No univalence of a
whole Fatou component is assumed.
-/

open Set Metric Function Filter
open scoped Topology

namespace AreaDeficit

/-- Eventual avoidance of singular values by the successor intrinsic discs
gives eventual injectivity on the preceding discs. -/
theorem eventually_injOn_chartDisc_of_chartDisc_avoid_singularValues
    {f : ℂ → ℂ} {U : ℕ → Set ℂ} {u : ℕ → ℂ → ℂ} {z : ℕ → ℂ}
    (hU : ∀ n, IsOpen (U n))
    (hu : ∀ n, DifferentiableOn ℂ (u n) (U n))
    (hub : ∀ n, BijOn (u n) (U n) (ball 0 1))
    (hz : ∀ n, z n ∈ U n) (hu0 : ∀ n, u n (z n) = 0)
    (hznext : ∀ n, f (z n) = z (n + 1))
    (hf : Differentiable ℂ f)
    (hfm : ∀ n, MapsTo f (U n) (U (n + 1)))
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (havoid : ∀ᶠ n in atTop,
      Disjoint (chartDisc (u (n + 1)) (U (n + 1)) r)
        (ComplexDynamics.singularValues f)) :
    ∀ᶠ n in atTop, InjOn f (chartDisc (u n) (U n) r) := by
  filter_upwards [havoid] with n hn
  have hsourceOpen := chartDisc_isOpen (hU n) (hu n) r
  have htargetOpen := chartDisc_isOpen (hU (n + 1)) (hu (n + 1)) r
  have hsourceSC := chartDisc_isSimplyConnected (hU n) (hu n) (hub n) hr hr1
  have htargetSC := chartDisc_isSimplyConnected
    (hU (n + 1)) (hu (n + 1)) (hub (n + 1)) hr hr1
  have hzsource : z n ∈ chartDisc (u n) (U n) r := by
    refine ⟨hz n, ?_⟩
    simpa only [mem_preimage, hu0 n] using (mem_ball_self hr : (0 : ℂ) ∈ ball 0 r)
  have hmaps : MapsTo f (chartDisc (u n) (U n) r)
      (chartDisc (u (n + 1)) (U (n + 1)) r) :=
    mapsTo_chartDisc (hU n) (hu n) (hub n) (hu (n + 1))
      (hub (n + 1)).mapsTo hf.differentiableOn (hfm n)
      (hz n) (hu0 n) (by rw [hznext n, hu0 (n + 1)]) hr1
  apply singular_covering_injOn_domain hsourceOpen hsourceSC htargetOpen htargetSC
    hzsource hf.continuous.continuousOn hmaps
  intro w hw hsing
  exact Set.disjoint_left.mp hn hw hsing

/-- Eventual avoidance of singular values by successor domains gives eventual
injectivity on every fixed intrinsic disc. -/
theorem eventually_injOn_chartDisc_of_avoid_singularValues
    {f : ℂ → ℂ} {U : ℕ → Set ℂ} {u : ℕ → ℂ → ℂ} {z : ℕ → ℂ}
    (hU : ∀ n, IsOpen (U n))
    (hu : ∀ n, DifferentiableOn ℂ (u n) (U n))
    (hub : ∀ n, BijOn (u n) (U n) (ball 0 1))
    (hz : ∀ n, z n ∈ U n) (hu0 : ∀ n, u n (z n) = 0)
    (hznext : ∀ n, f (z n) = z (n + 1))
    (hf : Differentiable ℂ f)
    (hfm : ∀ n, MapsTo f (U n) (U (n + 1)))
    (havoid : ∀ᶠ n in atTop,
      Disjoint (U (n + 1)) (ComplexDynamics.singularValues f))
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∀ᶠ n in atTop, InjOn f (chartDisc (u n) (U n) r) := by
  apply eventually_injOn_chartDisc_of_chartDisc_avoid_singularValues
    hU hu hub hz hu0 hznext hf hfm hr hr1
  filter_upwards [havoid] with n hn
  exact hn.mono_left inter_subset_left

end AreaDeficit

#print axioms AreaDeficit.eventually_injOn_chartDisc_of_avoid_singularValues
#print axioms AreaDeficit.eventually_injOn_chartDisc_of_chartDisc_avoid_singularValues
