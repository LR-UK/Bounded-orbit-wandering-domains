module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.CoveringTotalArea
public import BoundedWanderingDomains.UnnormalisedPointRemoval
public import RiemannDynamics.Uniformization.PuncturedPlaneCovering
public import Mathlib.Analysis.Normed.Module.Connected

@[expose] public section

/-!
# Curvature minus one area of a finitely punctured plane

The intrinsic density defined componentwise agrees with the density of the
global disc covering.  Hence its curvature `-1` area is finite (and has the
expected exact value).
-/

open Set MeasureTheory
open scoped ENNReal Topology

namespace AreaDeficit

/-- The extremal characterisation identifies any valid finite-puncture
input with the intrinsic density. This follows by applying recovery to a
constant exhaustion. -/
theorem FinitePunctureMetricInput.density_eq_closedComplement
    (G : FinitePunctureMetricInput) (P : Finset ℂ)
    {a b z : ℂ} (hab : a ≠ b) (ha : a ∈ P) (hb : b ∈ P) (hz : z ∉ P) :
    G.density P z = closedComplementDensity (↑P : Set ℂ)
      P.finite_toSet.isClosed hab ha hb z := by
  have ht := G.density_tendsto_closedComplement (P := fun _ => P)
    (fun _ _ _ => Finset.Subset.refl P) hab ha hb
    (by simpa only [iUnion_const, P.finite_toSet.isClosed.closure_eq, Finset.mem_coe] using hz)
  have ht' : Filter.Tendsto (fun _ : ℕ => G.density P z) Filter.atTop
      (𝓝 (closedComplementDensity (↑P : Set ℂ) P.finite_toSet.isClosed hab ha hb z)) := by
    simpa only [iUnion_const, P.finite_toSet.isClosed.closure_eq] using ht
  exact tendsto_nhds_unique tendsto_const_nhds ht'

private theorem finite_complement_connectedComponentIn
    (P : Finset ℂ) {z : ℂ} (hz : z ∉ P) :
    connectedComponentIn ((↑P : Set ℂ)ᶜ) z = ((↑P : Set ℂ)ᶜ) := by
  apply IsPreconnected.connectedComponentIn _ hz
  exact (P.finite_toSet.countable.isPathConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected

/-- A global uniformising covering of a finitely punctured plane computes
the intrinsic density at every point outside the punctures. -/
theorem closedComplementDensity_eq_finite_cover
    {P : Finset ℂ} {p : ℂ → ℂ}
    (hp : IsHolomorphicDiscCovering p ((↑P : Set ℂ)ᶜ))
    {a b z : ℂ} (hab : a ≠ b) (ha : a ∈ P) (hb : b ∈ P)
    (hz : z ∉ P) :
    closedComplementDensity (↑P : Set ℂ) P.finite_toSet.isClosed
      hab ha hb z = coveringDensity p z := by
  apply closedComplementDensity_eq_cover (↑P : Set ℂ)
    P.finite_toSet.isClosed hab ha hb hz
  simpa only [finite_complement_connectedComponentIn P hz] using hp

/-- Exact total area of a finitely punctured plane for the intrinsic
curvature `-1` metric. -/
theorem finite_puncture_hyperbolicArea
    (P : Finset ℂ) (hP : 2 ≤ P.card)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ P) (hb : b ∈ P) :
    (∫⁻ z : ℂ, hyperbolicAreaWeight (↑P : Set ℂ)
      P.finite_toSet.isClosed hab ha hb z) =
      ((P.card : ℝ≥0∞) - 1) * ENNReal.ofReal (2 * Real.pi) := by
  obtain ⟨p, hp⟩ :=
    RiemannDynamics.exists_disc_covering_finitely_punctured_plane P hP
  let c : ℝ≥0∞ := ENNReal.ofReal (2 * Real.pi)
  have hnull : ∀ᵐ z : ℂ ∂volume, z ∉ P := by
    rw [ae_iff]
    simp only [not_not]
    exact P.finite_toSet.measure_zero volume
  calc
    (∫⁻ z : ℂ, hyperbolicAreaWeight (↑P : Set ℂ)
        P.finite_toSet.isClosed hab ha hb z) =
        (∫⁻ z : ℂ, closedComplementAreaWeight (↑P : Set ℂ)
          P.finite_toSet.isClosed hab ha hb z) * c := by
          rw [← lintegral_mul_const c
            (measurable_closedComplementAreaWeight
              (↑P : Set ℂ) P.finite_toSet.isClosed hab ha hb)]
          apply lintegral_congr
          intro z
          exact hyperbolicAreaWeight_eq_normalised_mul
            (↑P : Set ℂ) P.finite_toSet.isClosed hab ha hb z
    _ = (∫⁻ z : ℂ,
        ENNReal.ofReal ((coveringDensity p z)^2 / (2 * Real.pi))) * c := by
          congr 1
          apply lintegral_congr_ae
          filter_upwards [hnull] with z hz
          unfold closedComplementAreaWeight
          rw [closedComplementDensity_eq_finite_cover hp hab ha hb hz]
    _ = (P.card - 1 : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi) := by
          rw [hp.total_area hP]
          simp only [ENNReal.natCast_sub, Nat.cast_one, c]

/-- In particular, the intrinsic curvature `-1` area measure of a finite
puncture model has finite total mass. -/
theorem finite_puncture_hyperbolicArea_ne_top
    (P : Finset ℂ) (hP : 2 ≤ P.card)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ P) (hb : b ∈ P) :
    (∫⁻ z : ℂ, hyperbolicAreaWeight (↑P : Set ℂ)
      P.finite_toSet.isClosed hab ha hb z) ≠ ∞ := by
  rw [finite_puncture_hyperbolicArea P hP hab ha hb]
  exact ENNReal.mul_ne_top (ENNReal.sub_ne_top (ENNReal.natCast_ne_top _))
    ENNReal.ofReal_ne_top

end AreaDeficit
