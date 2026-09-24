/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.GeneralDensityLimit
import BoundedWanderingDomains.GeneralDomainMetric
import BoundedWanderingDomains.AreaLimits
import BoundedWanderingDomains.LocalIntegratedDeficit
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# Area gained by puncturing a hyperbolic domain

The existing total-area formula gives the exact cost for a finite puncture
model. Fatou transfers a uniform bound on the nonnegative density difference
to limiting domains, without subtracting infinite total areas.
-/

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace AreaDeficit

/-- Fatou applied to a difference of pointwise convergent area densities.
Finiteness of one limiting density prevents infinity minus infinity. -/
theorem limiting_gain_bound {α : Type*} [MeasurableSpace α]
    {m : Measure α} {B : Set α} {a b : ℕ → α → ℝ≥0∞}
    {v w : α → ℝ≥0∞} {C : ℝ≥0∞}
    (ha : ∀ n, AEMeasurable (a n) (m.restrict B))
    (hb : ∀ n, AEMeasurable (b n) (m.restrict B))
    (hta : ∀ᵐ x ∂m.restrict B, Tendsto (fun n => a n x) atTop (𝓝 (v x)))
    (htb : ∀ᵐ x ∂m.restrict B, Tendsto (fun n => b n x) atTop (𝓝 (w x)))
    (hfin : ∀ᵐ x ∂m.restrict B, v x ≠ ∞ ∨ w x ≠ ∞)
    (hbound : ∀ n, (∫⁻ x in B, a n x - b n x ∂m) ≤ C) :
    (∫⁻ x in B, v x - w x ∂m) ≤ C := by
  apply limiting_area_bound (fun n => (ha n).sub (hb n)) _ hbound
  filter_upwards [hta, htb, hfin] with x hax hbx hfx
  exact ENNReal.Tendsto.sub hax hbx hfx

namespace FinitePunctureMetricInput

/-- Curvature −1 area density divided by 2π. -/
noncomputable def areaWeight (G : FinitePunctureMetricInput)
    (P : Finset ℂ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((G.density P z)^2 / (2 * Real.pi))

/-- Pointwise metric convergence gives area density convergence. -/
theorem areaWeight_tendsto_component_cover (G : FinitePunctureMetricInput)
    {P : ℕ → Finset ℂ} (hP : Monotone P)
    {a b z : ℂ} (hab : a ≠ b) (ha : a ∈ P 0) (hb : b ∈ P 0)
    (hz : z ∉ closure (⋃ n, (↑(P n) : Set ℂ)))
    {q : ℂ → ℂ}
    (hq : IsHolomorphicDiscCovering q (connectedComponentIn
      (closure (⋃ n, (↑(P n) : Set ℂ)))ᶜ z)) :
    Tendsto (fun n => G.areaWeight (P n) z) atTop
      (𝓝 (ENNReal.ofReal ((coveringDensity q z)^2 / (2 * Real.pi)))) := by
  have ht := G.density_tendsto_component_cover hP hab ha hb hz hq
  exact ENNReal.tendsto_ofReal ((ht.pow 2).div_const _)

/-- The finite models converge to the intrinsic area density on the
component of the limiting plane domain. -/
theorem areaWeight_tendsto_closedComplement (G : FinitePunctureMetricInput)
    {P : ℕ → Finset ℂ} (hP : Monotone P)
    {a b z : ℂ} (hab : a ≠ b) (ha : a ∈ P 0) (hb : b ∈ P 0)
    (hz : z ∉ closure (⋃ n, (↑(P n) : Set ℂ))) :
    Tendsto (fun n => G.areaWeight (P n) z) atTop
      (𝓝 (closedComplementAreaWeight (closure (⋃ n, (↑(P n) : Set ℂ)))
        isClosed_closure hab
        (subset_closure (mem_iUnion.mpr ⟨0, ha⟩))
        (subset_closure (mem_iUnion.mpr ⟨0, hb⟩)) z)) := by
  have ht := G.density_tendsto_closedComplement hP hab ha hb hz
  exact ENNReal.tendsto_ofReal ((ht.pow 2).div_const _)

/-- In a finite puncture model, the density difference integrates to at
most the number of newly removed points. -/
theorem finite_puncture_gain_bound (G : FinitePunctureMetricInput)
    {P E : Finset ℂ} (hP : 2 ≤ P.card) :
    (∫⁻ z : ℂ, G.areaWeight (P ∪ E) z - G.areaWeight P z) ≤
      ((E \ P).card : ℝ≥0∞) := by
  have hmeas : Measurable (G.areaWeight P) :=
    (((G.measurable_density hP).pow_const 2).div_const _).ennreal_ofReal
  have hμfin : (∫⁻ z : ℂ, G.areaWeight P z) ≠ ∞ := by
    have hf := G.area_finite P hP
    simp only [area, withDensity_apply _ MeasurableSet.univ] at hf
    simpa only [areaWeight, Measure.restrict_univ] using hf
  have hmono : (G.areaWeight P) ≤ᵐ[volume] (G.areaWeight (P ∪ E)) := by
    have havoid : ∀ᵐ z : ℂ ∂volume, z ∉ P ∪ E := by
      rw [ae_iff]
      simp only [not_not]
      exact (P ∪ E).finite_toSet.measure_zero volume
    filter_upwards [havoid] with z hz
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hp := le_of_lt (G.positive P hP z (fun h => hz (Finset.mem_union_left E h)))
    have hm := G.density_mono hP Finset.subset_union_left hz
    nlinarith
  rw [lintegral_sub hmeas hμfin hmono]
  have hcost := G.insertion_area_cost (E := E) hP (B := univ) MeasurableSet.univ
  simp only [area, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hcost
  apply (tsub_le_iff_right).mpr
  simpa only [areaWeight, add_comm] using hcost

/-- Metric limits inherit the finite-puncture gain bound. This theorem
explicitly assumes the almost-everywhere metric convergence. -/
theorem puncture_gain_bound_of_metric_limits (G : FinitePunctureMetricInput)
    {P : ℕ → Finset ℂ} {E : Finset ℂ} (hP : ∀ n, 2 ≤ (P n).card)
    {B : Set ℂ} {v w : ℂ → ℝ≥0∞}
    (hlimNew : ∀ᵐ z ∂volume.restrict B,
      Tendsto (fun n => G.areaWeight (P n ∪ E) z) atTop (𝓝 (v z)))
    (hlimOld : ∀ᵐ z ∂volume.restrict B,
      Tendsto (fun n => G.areaWeight (P n) z) atTop (𝓝 (w z)))
    (hfinite : ∀ᵐ z ∂volume.restrict B, w z ≠ ∞) :
    (∫⁻ z in B, v z - w z) ≤ (E.card : ℝ≥0∞) := by
  have hQ : ∀ n, 2 ≤ (P n ∪ E).card := fun n =>
    (hP n).trans (Finset.card_le_card Finset.subset_union_left)
  have hw (Q : Finset ℂ) (hQ : 2 ≤ Q.card) : Measurable (G.areaWeight Q) :=
    (((G.measurable_density hQ).pow_const 2).div_const _).ennreal_ofReal
  apply limiting_gain_bound
    (fun n => (hw _ (hQ n)).aemeasurable)
    (fun n => (hw _ (hP n)).aemeasurable)
    hlimNew hlimOld (hfinite.mono (fun _ h => Or.inr h))
  intro n
  calc
    (∫⁻ z in B, G.areaWeight (P n ∪ E) z - G.areaWeight (P n) z) ≤
      ∫⁻ z : ℂ, G.areaWeight (P n ∪ E) z - G.areaWeight (P n) z := by
        simpa only [Measure.restrict_univ] using
          (lintegral_mono_set (μ := (volume : Measure ℂ))
            (f := fun z => G.areaWeight (P n ∪ E) z - G.areaWeight (P n) z)
            (subset_univ B))
    _ ≤ ((E \ P n).card : ℝ≥0∞) := G.finite_puncture_gain_bound (hP n)
    _ ≤ (E.card : ℝ≥0∞) := by
      exact_mod_cast Finset.card_le_card Finset.sdiff_subset

/-- The finite-puncture cost survives an exhaustion of a closed deleted set.
The two closure equalities express that the chosen finite sets exhaust the
deleted sets; the estimate itself is independent of the exhaustion. -/
theorem puncture_gain_bound_closed_exhaustion (G : FinitePunctureMetricInput)
    {P : ℕ → Finset ℂ} (hP : Monotone P)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ P 0) (hb : b ∈ P 0)
    (E : Finset ℂ) (A A' : Set ℂ) (hA : IsClosed A) (hA' : IsClosed A')
    (hinc : A ⊆ A')
    (hrep : A = closure (⋃ n, (↑(P n) : Set ℂ)))
    (hrep' : A' = closure (⋃ n, (↑(P n ∪ E) : Set ℂ)))
    (haA : a ∈ A) (hbA : b ∈ A) (haA' : a ∈ A') (hbA' : b ∈ A') :
    (∫⁻ z in A'ᶜ,
      closedComplementAreaWeight A' hA' hab haA' hbA' z -
        closedComplementAreaWeight A hA hab haA hbA z) ≤ (E.card : ℝ≥0∞) := by
  have hQ : Monotone (fun n => P n ∪ E) := by
    intro i j hij
    exact Finset.union_subset_union_left (hP hij)
  have hcard : ∀ n, 2 ≤ (P n).card := by
    intro n
    have htwo : ({a, b} : Finset ℂ).card = 2 := by simp [hab]
    rw [← htwo]
    exact Finset.card_le_card (Finset.insert_subset_iff.mpr
      ⟨(hP (Nat.zero_le n)) ha, Finset.singleton_subset_iff.mpr ((hP (Nat.zero_le n)) hb)⟩)
  have hB : MeasurableSet A'ᶜ := hA'.isOpen_compl.measurableSet
  have hzB : ∀ᵐ z : ℂ ∂volume.restrict A'ᶜ, z ∈ A'ᶜ := ae_restrict_mem hB
  have hnew : ∀ᵐ z : ℂ ∂volume.restrict A'ᶜ,
      Tendsto (fun n => G.areaWeight (P n ∪ E) z) atTop
        (𝓝 (closedComplementAreaWeight A' hA' hab haA' hbA' z)) := by
    filter_upwards [hzB] with z hz
    have ht := G.areaWeight_tendsto_closedComplement hQ hab
      (Finset.mem_union_left E ha) (Finset.mem_union_left E hb)
      (show z ∉ closure (⋃ n, (↑(P n ∪ E) : Set ℂ)) from hrep' ▸ hz)
    simpa only [← hrep'] using ht
  have hold : ∀ᵐ z : ℂ ∂volume.restrict A'ᶜ,
      Tendsto (fun n => G.areaWeight (P n) z) atTop
        (𝓝 (closedComplementAreaWeight A hA hab haA hbA z)) := by
    filter_upwards [hzB] with z hz
    have ht := G.areaWeight_tendsto_closedComplement hP hab ha hb
      (show z ∉ closure (⋃ n, (↑(P n) : Set ℂ)) from
        hrep ▸ (fun h : z ∈ A => hz (hinc h)))
    simpa only [← hrep] using ht
  exact G.puncture_gain_bound_of_metric_limits hcard hnew hold
    (Filter.Eventually.of_forall (fun z => ENNReal.ofReal_ne_top))

end FinitePunctureMetricInput
end AreaDeficit

#print axioms AreaDeficit.limiting_gain_bound
#print axioms AreaDeficit.FinitePunctureMetricInput.finite_puncture_gain_bound
#print axioms AreaDeficit.FinitePunctureMetricInput.areaWeight_tendsto_component_cover
#print axioms AreaDeficit.FinitePunctureMetricInput.puncture_gain_bound_of_metric_limits
