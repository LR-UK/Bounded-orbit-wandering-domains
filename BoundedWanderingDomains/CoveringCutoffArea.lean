/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.CoveringEndIntegrals
import BoundedWanderingDomains.PuncturedCutoff

open Set Filter MeasureTheory InnerProductSpace Laplacian Metric
open scoped Topology ContDiff

namespace AreaDeficit

theorem finset_punctured_ball (P : Finset ℂ) (a : ℂ) :
    ∃ R > 0, ball a R \ {a} ⊆ (↑P : Set ℂ)ᶜ := by
  classical
  have hopen : IsOpen ((↑(P.erase a) : Set ℂ)ᶜ) := (P.erase a).finite_toSet.isClosed.isOpen_compl
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hopen a (by simp)
  refine ⟨R, hR, ?_⟩
  intro z hz hzP
  exact hball hz.1 (by simpa [and_comm] using Finset.mem_erase.mpr ⟨hz.2, hzP⟩)

theorem finset_exterior (P : Finset ℂ) (a : ℂ) :
    ∃ R > 0, {z : ℂ | R < ‖z - a‖} ⊆ (↑P : Set ℂ)ᶜ := by
  refine ⟨(∑ b ∈ P, ‖b - a‖) + 1, ?_, ?_⟩
  · have : 0 ≤ ∑ b ∈ P, ‖b - a‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  · intro z hz hzP
    have : ‖z - a‖ ≤ ∑ b ∈ P, ‖b - a‖ :=
      Finset.single_le_sum (fun b _ => norm_nonneg (b - a)) hzP
    dsimp only [mem_ofPred_eq] at hz
    linarith

theorem IsHolomorphicDiscCovering.cutoff_green {P : Finset ℂ} {p : ℂ → ℂ}
    (hp : IsHolomorphicDiscCovering p (↑P : Set ℂ)ᶜ) {c : ℂ} {t : ℝ}
    (ht : CutoffSeparated P c t) :
    (∫ z : ℂ, puncturedCutoff P c t z * (coveringDensity p z)^2) =
      ∫ z : ℂ, Real.log (coveringDensity p z) * Δ (puncturedCutoff P c t) z := by
  rw [← green_laplacian
    (fun z hz => hp.log_density_contDiffAt (puncturedCutoff_tsupport_avoids ht hz))
    ((puncturedCutoff_contDiff P c ht.1).of_le (by norm_num))
    (puncturedCutoff_hasCompactSupport P c ht.1)]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ tsupport (puncturedCutoff P c t)
  · rw [hp.density_curvature (puncturedCutoff_tsupport_avoids ht hz)]
  · simp [image_eq_zero_of_notMem_tsupport hz]

theorem IsHolomorphicDiscCovering.integrable_cutoff_density {P : Finset ℂ} {p : ℂ → ℂ}
    (hp : IsHolomorphicDiscCovering p (↑P : Set ℂ)ᶜ) {c : ℂ} {t : ℝ}
    (ht : CutoffSeparated P c t) :
    Integrable (fun z : ℂ => puncturedCutoff P c t z * (coveringDensity p z)^2) :=
  integrable_mul_of_local (puncturedCutoff_contDiff P c ht.1).continuous
    (puncturedCutoff_hasCompactSupport P c ht.1) (fun _z hz =>
      (hp.density_contDiffAt (puncturedCutoff_tsupport_avoids ht hz)).continuousAt.pow 2)

/-- The curvature integrals with all cusps cut off tend to the expected total area. -/
theorem IsHolomorphicDiscCovering.tendsto_cutoff_area {P : Finset ℂ} {p : ℂ → ℂ}
    (hp : IsHolomorphicDiscCovering p (↑P : Set ℂ)ᶜ) (hP : 2 ≤ P.card)
    {c : ℂ} (hc : c ∈ P) :
    Tendsto (fun t : ℝ => ∫ z : ℂ,
      puncturedCutoff P c t z * (coveringDensity p z)^2)
      atTop (𝓝 (2 * Real.pi * ((P.card : ℝ) - 1))) := by
  have hfinite (a : ℂ) (ha : a ∈ P) := finset_punctured_ball P a
  obtain ⟨R, hR, hout⟩ := finset_exterior P c
  obtain ⟨b, hb, hbc⟩ := Finset.exists_mem_ne (by omega : 1 < P.card) c
  have houter := hp.integral_infinite_end hbc.symm (by simpa using hc) (by simpa using hb) hR hout
  have hinner (a : ℂ) (ha : a ∈ P) : Tendsto (fun t : ℝ => ∫ z : ℂ,
      Real.log (coveringDensity p z) * Δ (logCutoff a (-2*t) (-t)) z)
      atTop (𝓝 (-2 * Real.pi)) := by
    obtain ⟨d, hd, hda⟩ := Finset.exists_mem_ne (by omega : 1 < P.card) a
    obtain ⟨r, hr, hball⟩ := hfinite a ha
    exact hp.integral_finite_end hda.symm (by simpa using ha) (by simpa using hd) hr hball
  have hsum := tendsto_finsetSum P hinner
  have hlim := houter.sub hsum
  have hval : (-2 * Real.pi) - (∑ _a ∈ P, (-2 * Real.pi)) =
      2 * Real.pi * ((P.card : ℝ) - 1) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hval] at hlim
  apply hlim.congr'
  have hi : ∀ᶠ t : ℝ in atTop, ∀ a ∈ P, Integrable (fun z : ℂ =>
      Real.log (coveringDensity p z) * Δ (logCutoff a (-2*t) (-t)) z) := by
    rw [eventually_all_finset]
    intro a ha
    obtain ⟨r, hr, hball⟩ := hfinite a ha
    exact hp.integrable_finite_end hr hball
  filter_upwards [eventually_cutoffSeparated P c, hp.integrable_infinite_end hout, hi]
    with t ht hio hii
  rw [hp.cutoff_green ht]
  simp_rw [laplacian_puncturedCutoff P c _ ht.1, mul_sub, Finset.mul_sum]
  rw [integral_sub hio (integrable_finsetSum P hii), integral_finsetSum P hii]

end AreaDeficit
