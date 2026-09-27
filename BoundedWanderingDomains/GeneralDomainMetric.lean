/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.GeneralDomainCovering
import BoundedWanderingDomains.GeneralDensityLimit
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Hyperbolic density of a plane domain

For a closed planar set containing two distinct points, uniformisation gives
the disc covering of each component of its complement. The resulting density
is intrinsic to the domain, independent of every choice of covering.
-/

open Set Filter
open scoped Topology ENNReal

namespace AreaDeficit

/-- Hyperbolic density of the complement of a closed set, set to zero on
the deleted set. The proofs of closedness and the two omitted values are
explicit parameters; they are not additional assumptions about the domain. -/
noncomputable def closedComplementDensity (A : Set ℂ) (hA : IsClosed A)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A)
    (z : ℂ) : ℝ := by
  classical
  exact if hz : z ∉ A then
    coveringDensity (Classical.choose
      (RiemannDynamics.exists_disc_covering_complement_component hA hz hab ha hb)) z
    else 0

/-- Any disc covering of the point's component computes this density. -/
theorem closedComplementDensity_eq_cover (A : Set ℂ) (hA : IsClosed A)
    {a b z : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A)
    (hz : z ∉ A) {q : ℂ → ℂ}
    (hq : IsHolomorphicDiscCovering q (connectedComponentIn Aᶜ z)) :
    closedComplementDensity A hA hab ha hb z = coveringDensity q z := by
  simp only [closedComplementDensity, dite_eq_left hz]
  exact (Classical.choose_spec
    (RiemannDynamics.exists_disc_covering_complement_component hA hz hab ha hb))
      |>.coveringDensity_eq hq (mem_connectedComponentIn hz)

/-- The canonical density is strictly positive throughout the domain. -/
theorem closedComplementDensity_pos (A : Set ℂ) (hA : IsClosed A)
    {a b z : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A)
    (hz : z ∉ A) : 0 < closedComplementDensity A hA hab ha hb z := by
  obtain ⟨q, hq⟩ :=
    RiemannDynamics.exists_disc_covering_complement_component hA hz hab ha hb
  rw [closedComplementDensity_eq_cover A hA hab ha hb hz hq]
  exact hq.density_pos (mem_connectedComponentIn hz)

/-- Removing more points can only increase the intrinsic hyperbolic density
on the common domain. This needs no finite-puncture metric input. -/
theorem closedComplementDensity_mono (A B : Set ℂ)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : A ⊆ B)
    {a b z : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A)
    (hz : z ∉ B) :
    closedComplementDensity A hA hab ha hb z ≤
      closedComplementDensity B hB hab (hAB ha) (hAB hb) z := by
  have hzA : z ∉ A := fun h => hz (hAB h)
  obtain ⟨p, hp⟩ :=
    RiemannDynamics.exists_disc_covering_complement_component hA hzA hab ha hb
  obtain ⟨q, hq⟩ :=
    RiemannDynamics.exists_disc_covering_complement_component hB hz hab (hAB ha) (hAB hb)
  rw [closedComplementDensity_eq_cover A hA hab ha hb hzA hp,
    closedComplementDensity_eq_cover B hB hab (hAB ha) (hAB hb) hz hq]
  obtain ⟨g, hgdiff, hgmap, hg0, hgext⟩ :=
    hq.density_extremal (mem_connectedComponentIn hz)
  have hgmapA : MapsTo g (Metric.ball 0 1) (connectedComponentIn Aᶜ z) :=
    hgmap.mono_right (connectedComponentIn_mono z (Set.compl_subset_compl.mpr hAB))
  have hs := hp.density_schwarz hgdiff hgmapA
  rw [hg0] at hs
  have hnorm : 0 < ‖deriv g 0‖ := by
    have hne : ‖deriv g 0‖ ≠ 0 := by
      intro heq
      rw [heq, mul_zero] at hgext
      norm_num at hgext
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  exact (mul_le_mul_iff_left₀ hnorm).mp (hs.trans_eq hgext.symm)

/-- One fixed covering computes the canonical density throughout its
connected component. -/
theorem closedComplementDensity_eqOn_component (A : Set ℂ) (hA : IsClosed A)
    {a b z : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A)
    {q : ℂ → ℂ}
    (hq : IsHolomorphicDiscCovering q (connectedComponentIn Aᶜ z)) :
    EqOn (closedComplementDensity A hA hab ha hb) (coveringDensity q)
      (connectedComponentIn Aᶜ z) := by
  intro w hw
  have hwA : w ∉ A := connectedComponentIn_subset _ _ hw
  have hqw : IsHolomorphicDiscCovering q (connectedComponentIn Aᶜ w) :=
    (connectedComponentIn_eq hw) ▸ hq
  exact closedComplementDensity_eq_cover A hA hab ha hb hwA hqw

/-- The canonical density is twice continuously differentiable inside the
domain, even though its definition chooses a covering separately at each
point. -/
theorem closedComplementDensity_contDiffAt (A : Set ℂ) (hA : IsClosed A)
    {a b z : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A)
    (hz : z ∉ A) :
    ContDiffAt ℝ 2 (closedComplementDensity A hA hab ha hb) z := by
  obtain ⟨q, hq⟩ :=
    RiemannDynamics.exists_disc_covering_complement_component hA hz hab ha hb
  have hUopen : IsOpen (connectedComponentIn Aᶜ z) :=
    hA.isOpen_compl.connectedComponentIn
  have heq : closedComplementDensity A hA hab ha hb =ᶠ[𝓝 z] coveringDensity q :=
    Filter.mem_of_superset (hUopen.mem_nhds (mem_connectedComponentIn hz))
      (closedComplementDensity_eqOn_component A hA hab ha hb hq)
  exact (hq.density_contDiffAt (mem_connectedComponentIn hz)).congr_of_eventuallyEq heq

/-- The canonical density has curvature −1 on each component. -/
theorem closedComplementDensity_curvature (A : Set ℂ) (hA : IsClosed A)
    {a b z : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A)
    (hz : z ∉ A) :
    Laplacian.laplacian (fun t => Real.log (closedComplementDensity A hA hab ha hb t)) z =
      (closedComplementDensity A hA hab ha hb z)^2 := by
  obtain ⟨q, hq⟩ :=
    RiemannDynamics.exists_disc_covering_complement_component hA hz hab ha hb
  have hUopen : IsOpen (connectedComponentIn Aᶜ z) :=
    hA.isOpen_compl.connectedComponentIn
  have heq : closedComplementDensity A hA hab ha hb =ᶠ[𝓝 z] coveringDensity q :=
    Filter.mem_of_superset (hUopen.mem_nhds (mem_connectedComponentIn hz))
      (closedComplementDensity_eqOn_component A hA hab ha hb hq)
  have hlog := heq.fun_comp Real.log
  simp only [Function.comp_def] at hlog
  rw [(InnerProductSpace.laplacian_congr_nhds hlog).eq_of_nhds,
    heq.eq_of_nhds]
  exact hq.density_curvature (mem_connectedComponentIn hz)

/-- The componentwise hyperbolic density is measurable on the entire
plane, including the set where it has been extended by zero. -/
theorem measurable_closedComplementDensity (A : Set ℂ) (hA : IsClosed A)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A) :
    Measurable (closedComplementDensity A hA hab ha hb) := by
  classical
  let ρ := closedComplementDensity A hA hab ha hb
  have hc : ContinuousOn ρ Aᶜ := fun z hz =>
    (closedComplementDensity_contDiffAt A hA hab ha hb hz).continuousAt.continuousWithinAt
  have hp := hc.measurable_piecewise (continuousOn_const : ContinuousOn (fun _ : ℂ => (0 : ℝ)) Aᶜᶜ)
    hA.isOpen_compl.measurableSet
  convert hp using 1
  ext z
  by_cases hz : z ∉ A
  · simp [Set.piecewise, hz, ρ]
  · have hzA : z ∈ A := not_not.mp hz
    simp [Set.piecewise, ρ, closedComplementDensity, hzA]

/-- Finite-puncture densities converge to the canonical hyperbolic density
of the limiting component, with no covering among the assumptions. -/
theorem FinitePunctureMetricInput.density_tendsto_closedComplement
    (G : FinitePunctureMetricInput)
    {P : ℕ → Finset ℂ} (hP : Monotone P)
    {a b z : ℂ} (hab : a ≠ b) (ha : a ∈ P 0) (hb : b ∈ P 0)
    (hz : z ∉ closure (⋃ n, (↑(P n) : Set ℂ))) :
    Tendsto (fun n => G.density (P n) z) Filter.atTop
      (𝓝 (closedComplementDensity (closure (⋃ n, (↑(P n) : Set ℂ)))
        isClosed_closure hab
        (subset_closure (mem_iUnion.mpr ⟨0, ha⟩))
        (subset_closure (mem_iUnion.mpr ⟨0, hb⟩)) z)) := by
  obtain ⟨q, hq, ht⟩ := G.exists_cover_and_density_limit hP hab ha hb hz
  rw [closedComplementDensity_eq_cover _ isClosed_closure hab
    (subset_closure (mem_iUnion.mpr ⟨0, ha⟩))
    (subset_closure (mem_iUnion.mpr ⟨0, hb⟩)) hz hq]
  exact ht

/-- The normalised hyperbolic area density on a componentwise hyperbolic
plane domain. Multiplying by `2 * Real.pi` gives the curvature −1 area. -/
noncomputable def closedComplementAreaWeight (A : Set ℂ) (hA : IsClosed A)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((closedComplementDensity A hA hab ha hb z)^2 / (2 * Real.pi))

theorem measurable_closedComplementAreaWeight (A : Set ℂ) (hA : IsClosed A)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A) :
    Measurable (closedComplementAreaWeight A hA hab ha hb) :=
  (((measurable_closedComplementDensity A hA hab ha hb).pow_const 2).div_const _).ennreal_ofReal

/-- Monotonicity of the normalised area form away from the larger obstacle. -/
theorem closedComplementAreaWeight_mono (A B : Set ℂ)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : A ⊆ B)
    {a b z : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A)
    (hz : z ∉ B) :
    closedComplementAreaWeight A hA hab ha hb z ≤
      closedComplementAreaWeight B hB hab (hAB ha) (hAB hb) z := by
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hp := le_of_lt (closedComplementDensity_pos A hA hab ha hb (fun h => hz (hAB h)))
  have hm := closedComplementDensity_mono A B hA hB hAB hab ha hb hz
  nlinarith

end AreaDeficit
