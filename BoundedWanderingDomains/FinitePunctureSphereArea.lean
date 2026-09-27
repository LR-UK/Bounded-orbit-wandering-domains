/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.FinitePunctureArea
import BoundedWanderingDomains.SphereFiniteRemoval

/-! # Finite-puncture models as intrinsic sphere metrics -/

open Set Function OnePoint MeasureTheory
open scoped Topology RiemannSphere ENNReal

namespace AreaDeficit

/-- The spherical obstacle corresponding to a finite planar puncture set. -/
def finiteSphereObstacle (P : Finset ℂ) : Set (OnePoint ℂ) :=
  insert (∞ : OnePoint ℂ) (sphereFiniteSet P)

theorem isClosed_finiteSphereObstacle (P : Finset ℂ) :
    IsClosed (finiteSphereObstacle P) :=
  ((P.finite_toSet.image (fun z : ℂ => (z : OnePoint ℂ))).insert (∞ : OnePoint ℂ)).isClosed

@[simp] theorem coe_mem_finiteSphereObstacle (P : Finset ℂ) (z : ℂ) :
    (z : OnePoint ℂ) ∈ finiteSphereObstacle P ↔ z ∈ P := by
  simp [finiteSphereObstacle, sphereFiniteSet]

@[simp] theorem infty_chart_preimage_finiteSphereObstacle (P : Finset ℂ) :
    (spherePoleChart (∞ : OnePoint ℂ)) ⁻¹' finiteSphereObstacle P = (↑P : Set ℂ) := by
  ext z
  exact coe_mem_finiteSphereObstacle P z

/-- Standard finite-puncture coordinate witnesses; no metric properties
are assumed in this data. -/
def finiteSphereMetricData (P : Finset ℂ) {a b : ℂ}
    (hab : a ≠ b) (ha : a ∈ P) (hb : b ∈ P) :
    SphereHyperbolicMetricData (finiteSphereObstacle P) where
  pole := ∞
  pole_mem := Or.inl rfl
  anchorOne := a
  anchorTwo := b
  anchor_ne := hab
  anchorOne_mem := (coe_mem_finiteSphereObstacle P a).mpr ha
  anchorTwo_mem := (coe_mem_finiteSphereObstacle P b).mpr hb

/-- Sphere area in the standard chart is the actual curvature -1 planar
area on the set of finite coordinates. -/
theorem finiteSphereMetricData_area (P : Finset ℂ) {a b : ℂ}
    (hab : a ≠ b) (ha : a ∈ P) (hb : b ∈ P)
    (W : Set (OnePoint ℂ)) :
    sphereHyperbolicArea (finiteSphereObstacle P) (isClosed_finiteSphereObstacle P)
      (finiteSphereMetricData P hab ha hb) W =
      ∫⁻ z in ((fun z : ℂ => (z : OnePoint ℂ)) ⁻¹' W) ∩ (↑P : Set ℂ)ᶜ,
        hyperbolicAreaWeight (↑P : Set ℂ) P.finite_toSet.isClosed hab ha hb z := by
  unfold sphereHyperbolicArea
  simp only [finiteSphereMetricData, preimage_inter, preimage_compl,
    infty_chart_preimage_finiteSphereObstacle]
  rfl

/-- The intrinsic sphere metric of the finite model has exactly the
classical finite area, without any normalisation of area. -/
theorem finiteSphereMetricData_total_area (P : Finset ℂ) (hP : 2 ≤ P.card)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ P) (hb : b ∈ P) :
    sphereHyperbolicArea (finiteSphereObstacle P) (isClosed_finiteSphereObstacle P)
      (finiteSphereMetricData P hab ha hb) Set.univ =
      ((P.card : ℝ≥0∞) - 1) * ENNReal.ofReal (2 * Real.pi) := by
  rw [finiteSphereMetricData_area]
  simp only [preimage_univ, univ_inter]
  have hnull : (↑P : Set ℂ) =ᵐ[volume] ∅ := by
    rw [ae_eq_empty]
    exact P.finite_toSet.measure_zero volume
  have hc : (↑P : Set ℂ)ᶜ =ᵐ[volume] Set.univ := by
    filter_upwards [hnull] with x hx
    simpa using congrArg Not hx
  rw [setLIntegral_congr hc, setLIntegral_univ]
  exact finite_puncture_hyperbolicArea P hP hab ha hb

end AreaDeficit
