/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.DiscCoveringMetric
import BoundedWanderingDomains.HolomorphicTransport

/-!
# Area transport through an injective part of a disc covering

The density downstairs is independent of the chosen universal covering.
On any measurable subset of the disc on which the covering is injective,
its induced hyperbolic area is exactly the disc area. Thus a geometric
decomposition upstairs can be used without assuming area preservation.
-/

open Set Metric Function MeasureTheory
open scoped ENNReal

namespace AreaDeficit.IsHolomorphicDiscCovering

variable {p q : ℂ → ℂ} {S : Set ℂ}

/-- The induced density does not depend on which holomorphic disc covering
was selected. Both comparisons follow from the extremal-disc property. -/
theorem density_independent (hp : IsHolomorphicDiscCovering p S)
    (hq : IsHolomorphicDiscCovering q S) :
    EqOn (coveringDensity p) (coveringDensity q) S := by
  have hle {p q : ℂ → ℂ} (hp : IsHolomorphicDiscCovering p S)
      (hq : IsHolomorphicDiscCovering q S) {z : ℂ} (hz : z ∈ S) :
      coveringDensity p z ≤ coveringDensity q z := by
    obtain ⟨g, hg, hgm, hg0, he⟩ := hq.density_extremal hz
    have hs := hp.density_schwarz hg hgm
    rw [hg0] at hs
    have hd : 0 < ‖deriv g 0‖ := by
      by_contra h
      have hn : ‖deriv g 0‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
      simp [hn] at he
    exact (mul_le_mul_iff_left₀ hd).mp (hs.trans_eq he.symm)
  exact fun z hz => le_antisymm (hle hp hq hz) (hle hq hp hz)

/-- Pullback of the length density along the covering. -/
theorem density_pullback (hp : IsHolomorphicDiscCovering p S)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    ‖deriv p w‖ * coveringDensity p (p w) = discDensity w := by
  rw [hp.density_eq hw]
  exact mul_div_cancel₀ _ (norm_ne_zero_iff.mpr (hp.deriv_ne_zero hw))

/-- Change of variables identifies the actual covering-induced area,
including unbounded or infinite-area measurable subsets. -/
theorem area_image (hp : IsHolomorphicDiscCovering p S)
    {T : Set ℂ} (hT : MeasurableSet T) (hTD : T ⊆ ball 0 1)
    (hinj : InjOn p T) :
    (∫⁻ z in p '' T, ENNReal.ofReal ((coveringDensity p z)^2)) =
      ∫⁻ w in T, ENNReal.ofReal ((discDensity w)^2) := by
  rw [holomorphic_change_of_variables hT
    (fun w hw => hp.holo.hasDerivAt (isOpen_ball.mem_nhds (hTD hw))) hinj]
  apply setLIntegral_congr_fun hT
  intro w hw
  dsimp only
  rw [← ENNReal.ofReal_mul (sq_nonneg _), ← mul_pow,
    hp.density_pullback (hTD hw)]

/-- A finite geometric partition may be integrated upstairs, even though
the covering is globally many-to-one. Injectivity is required on each face,
and distinct face images must be disjoint. Boundaries are allowed to be null.
This proves the analytic transport step, not the existence of the partition. -/
theorem area_of_partition (hp : IsHolomorphicDiscCovering p S)
    {ι : Type*} [Fintype ι] (T : ι → Set ℂ)
    (hTo : ∀ i, IsOpen (T i)) (hTD : ∀ i, T i ⊆ ball 0 1)
    (hinj : ∀ i, InjOn p (T i))
    (hdis : Pairwise fun i j => Disjoint (p '' T i) (p '' T j))
    (hcover : (univ : Set ℂ) =ᵐ[volume] ⋃ i, p '' T i) :
    (∫⁻ z : ℂ, ENNReal.ofReal ((coveringDensity p z)^2)) =
      ∑ i, ∫⁻ w in T i, ENNReal.ofReal ((discDensity w)^2) := by
  let μ := volume.withDensity (fun z => ENNReal.ofReal ((coveringDensity p z)^2))
  have hi : ∀ i, MeasurableSet (p '' T i) := fun i =>
    (TauCeti.isOpen_image_of_differentiableOn_of_injOn
      (hTo i) (hp.holo.mono (hTD i)) (hinj i)).measurableSet
  have he : μ univ = μ (⋃ i, p '' T i) :=
    measure_congr ((withDensity_absolutelyContinuous _ _) hcover)
  rw [measure_iUnion hdis hi, tsum_fintype] at he
  simpa only [μ, withDensity_apply _ MeasurableSet.univ,
    withDensity_apply _ (hi _), Measure.restrict_univ,
    hp.area_image (hTo _).measurableSet (hTD _) (hinj _)] using he

end AreaDeficit.IsHolomorphicDiscCovering
