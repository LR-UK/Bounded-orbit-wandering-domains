import DiscMetric
import TotalAreaCost
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Tactic

/-!
# Classical input for finite-puncture hyperbolic geometry

This file defines a *parameter structure*, not an axiom or an instance.
An inhabitant must eventually be constructed from classical uniformisation
and Gauss–Bonnet. Until then, theorems taking this structure are conditional.

Only classical geometry is assumed here: positive smooth curvature −1
densities, the sharp disc Schwarz property, and normalised total area.
No puncture-limit, area-deficit, or dynamical theorem is a field.

The extremal-disc field is supplied by a normalised universal covering.
Its covering property is deliberately not needed for the deductions below.
-/

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal

namespace AreaDeficit

/-- Minimal classical metric data for planes with at least two punctures.
Density values *at* punctures have no geometric meaning and do not affect
the associated absolutely continuous measure. -/
structure FinitePunctureMetricInput where
  density : Finset ℂ → ℂ → ℝ
  positive : ∀ P : Finset ℂ, 2 ≤ P.card → ∀ z, z ∉ P → 0 < density P z
  smooth : ∀ P : Finset ℂ, 2 ≤ P.card →
    ContDiffOn ℝ 2 (density P) ((↑P : Set ℂ)ᶜ)
  curvature : ∀ P : Finset ℂ, 2 ≤ P.card → ∀ z, z ∉ P →
    Laplacian.laplacian (fun w => Real.log (density P w)) z = (density P z)^2
  schwarz : ∀ P : Finset ℂ, 2 ≤ P.card → ∀ p : ℂ → ℂ,
    DifferentiableOn ℂ p (ball 0 1) →
    MapsTo p (ball 0 1) ((↑P : Set ℂ)ᶜ) →
    density P (p 0) * ‖deriv p 0‖ ≤ 2
  extremal_disc : ∀ P : Finset ℂ, 2 ≤ P.card → ∀ z, z ∉ P →
    ∃ p : ℂ → ℂ, DifferentiableOn ℂ p (ball 0 1) ∧
      MapsTo p (ball 0 1) ((↑P : Set ℂ)ᶜ) ∧ p 0 = z ∧
      density P z * ‖deriv p 0‖ = 2
  total_area : ∀ P : Finset ℂ, 2 ≤ P.card →
    (∫⁻ z : ℂ, ENNReal.ofReal ((density P z)^2 / (2 * Real.pi))) =
      (P.card - 1 : ℕ)

namespace FinitePunctureMetricInput

variable (G : FinitePunctureMetricInput)

/-- The sharp disc Schwarz inequality with an arbitrary source radius. -/
theorem schwarz_on_ball {P : Finset ℂ} (hP : 2 ≤ P.card)
    {p : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hp : DifferentiableOn ℂ p (ball 0 r))
    (hm : MapsTo p (ball 0 r) ((↑P : Set ℂ)ᶜ)) :
    G.density P (p 0) * ‖deriv p 0‖ ≤ 2 / r := by
  let q : ℂ → ℂ := fun w => p ((r : ℂ) * w)
  have hscale : MapsTo (fun w : ℂ => (r : ℂ) * w) (ball 0 1) (ball 0 r) := by
    intro w hw
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    simpa using mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hw) hr
  have hq : DifferentiableOn ℂ q (ball 0 1) :=
    hp.comp (by fun_prop) hscale
  have hs := G.schwarz P hP q hq (hm.comp hscale)
  have hdp := hp.differentiableAt (ball_mem_nhds (0 : ℂ) hr)
  have hdq : deriv q 0 = deriv p 0 * (r : ℂ) := by
    have hp0 : HasDerivAt p (deriv p 0) ((r : ℂ) * 0) := by simpa using hdp.hasDerivAt
    simpa [q, Function.comp_def] using (hp0.comp 0 ((hasDerivAt_id (0 : ℂ)).const_mul (r : ℂ))).deriv
  dsimp [q] at hs
  change G.density P (p ((r : ℂ) * 0)) * ‖deriv q 0‖ ≤ 2 at hs
  rw [mul_zero, hdq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hs
  exact (le_div_iff₀ hr).mpr (by nlinarith)

/-- Normalised area, with curvature −1 and normalisation 1/(2π). -/
noncomputable def area (P : Finset ℂ) : Measure ℂ :=
  volume.withDensity (fun z => ENNReal.ofReal ((G.density P z)^2 / (2 * Real.pi)))

/-- Density monotonicity is derived from the sharp disc property; it is
not another assumed field of the classical input. -/
theorem density_mono {P Q : Finset ℂ} (hP : 2 ≤ P.card)
    (hPQ : P ⊆ Q) {z : ℂ} (hz : z ∉ Q) :
    G.density P z ≤ G.density Q z := by
  have hQ : 2 ≤ Q.card := hP.trans (Finset.card_le_card hPQ)
  obtain ⟨p, hp, hm, h0, he⟩ := G.extremal_disc Q hQ z hz
  have hmP : MapsTo p (ball 0 1) ((↑P : Set ℂ)ᶜ) := by
    intro w hw hmem
    exact hm hw (hPQ hmem)
  have hs := G.schwarz P hP p hp hmP
  rw [h0] at hs
  have hd : 0 < ‖deriv p 0‖ := by
    have hn := norm_nonneg (deriv p 0)
    have hnz : ‖deriv p 0‖ ≠ 0 := by
      intro h
      rw [h, mul_zero] at he
      norm_num at he
    exact lt_of_le_of_ne hn (Ne.symm hnz)
  exact (mul_le_mul_iff_left₀ hd).mp (hs.trans_eq he.symm)

theorem area_univ (P : Finset ℂ) (hP : 2 ≤ P.card) :
    G.area P univ = (P.card - 1 : ℕ) := by
  rw [area, withDensity_apply _ MeasurableSet.univ]
  simpa using G.total_area P hP

theorem area_finite (P : Finset ℂ) (hP : 2 ≤ P.card) :
    G.area P univ ≠ ∞ := by
  rw [G.area_univ P hP]
  exact ENNReal.natCast_ne_top _

/-- Measure monotonicity ignores the finitely many added punctures,
which are null for Euclidean area. -/
theorem area_mono {P Q : Finset ℂ} (hP : 2 ≤ P.card) (hPQ : P ⊆ Q) :
    G.area P ≤ G.area Q := by
  apply withDensity_mono
  have ha : ∀ᵐ z : ℂ ∂volume, z ∉ Q := by
    rw [ae_iff]
    simp only [not_not]
    exact Q.finite_toSet.measure_zero volume
  filter_upwards [ha] with z hz
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hp := le_of_lt (G.positive P hP z (fun h => hz (hPQ h)))
  have hm := G.density_mono hP hPQ hz
  nlinarith

/-- The area cost of inserting a finite set is now a proved consequence
of the classical input, not an assumed dynamical budget. -/
theorem insertion_area_cost {P E : Finset ℂ} (hP : 2 ≤ P.card)
    {B : Set ℂ} (hB : MeasurableSet B) :
    G.area (P ∪ E) B ≤ G.area P B + ((E \ P).card : ℝ≥0∞) := by
  classical
  have hQ : 2 ≤ (P ∪ E).card := hP.trans (Finset.card_le_card Finset.subset_union_left)
  apply area_cost_on_set_of_total_cost hB
    (G.area_mono hP Finset.subset_union_left) (G.area_finite P hP)
  rw [G.area_univ (P ∪ E) hQ, G.area_univ P hP, ← Nat.cast_add]
  have hc : (P ∪ E).card = P.card + (E \ P).card := by
    simpa [Finset.union_comm, Nat.add_comm] using (Finset.card_sdiff_add_card E P).symm
  have hn : (P ∪ E).card - 1 = P.card - 1 + (E \ P).card := by omega
  rw [hn]

end FinitePunctureMetricInput
end AreaDeficit

#print axioms AreaDeficit.FinitePunctureMetricInput.density_mono
#print axioms AreaDeficit.FinitePunctureMetricInput.insertion_area_cost
