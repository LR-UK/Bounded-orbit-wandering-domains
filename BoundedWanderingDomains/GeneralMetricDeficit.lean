module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.GeneralDomainMetric
public import BoundedWanderingDomains.DensityDeficit

@[expose] public section

/-!
# Curvature and the local hyperbolic area gain

These statements compare intrinsic hyperbolic densities of general plane
domains directly. No finite-puncture total-area formula is used.
-/

open Set MeasureTheory Filter InnerProductSpace Laplacian
open scoped Topology ContDiff ENNReal

namespace AreaDeficit

/-- Logarithmic gain in hyperbolic density after removing a closed set. -/
noncomputable def closedComplementLogGain (A B : Set ℂ)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : A ⊆ B)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A)
    (z : ℂ) : ℝ :=
  Real.log (closedComplementDensity B hB hab
    (hAB ha) (hAB hb) z) -
    Real.log (closedComplementDensity A hA hab ha hb z)

/-- The log gain is nonnegative on the smaller domain. -/
theorem closedComplementLogGain_nonneg (A B : Set ℂ)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : A ⊆ B)
    {a b z : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A)
    (hz : z ∉ B) :
    0 ≤ closedComplementLogGain A B hA hB hAB hab ha hb z := by
  dsimp [closedComplementLogGain]
  apply sub_nonneg.mpr
  exact Real.log_le_log
    (closedComplementDensity_pos A hA hab ha hb (fun h => hz (hAB h)))
    (closedComplementDensity_mono A B hA hB hAB hab ha hb hz)

/-- Both metrics have curvature minus one; the Laplacian of their log
ratio is the gain of squared density. -/
theorem closedComplementLogGain_laplacian (A B : Set ℂ)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : A ⊆ B)
    {a b z : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A)
    (hz : z ∉ B) :
    Δ (closedComplementLogGain A B hA hB hAB hab ha hb) z =
      (closedComplementDensity B hB hab (hAB ha) (hAB hb) z)^2 -
        (closedComplementDensity A hA hab ha hb z)^2 := by
  have hzA : z ∉ A := fun h => hz (hAB h)
  have hnew := (closedComplementDensity_contDiffAt B hB hab
    (hAB ha) (hAB hb) hz).log
      (ne_of_gt (closedComplementDensity_pos B hB hab (hAB ha) (hAB hb) hz))
  have hold := (closedComplementDensity_contDiffAt A hA hab ha hb hzA).log
    (ne_of_gt (closedComplementDensity_pos A hA hab ha hb hzA))
  have hsub := hnew.laplacian_sub hold
  change Δ ((fun i => Real.log (closedComplementDensity B hB hab (hAB ha) (hAB hb) i)) -
    (fun i => Real.log (closedComplementDensity A hA hab ha hb i))) z = _
  simpa only [closedComplementDensity_curvature B hB hab (hAB ha) (hAB hb) hz,
    closedComplementDensity_curvature A hA hab ha hb hzA] using hsub

/-- A bound for the logarithmic metric gain on a compactly supported cutoff
controls the gain of hyperbolic area there. This statement uses curvature
and integration by parts directly, with no finite-puncture area formula. -/
theorem closedComplement_gain_cutoff (A B : Set ℂ)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : A ⊆ B)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A)
    (chi : ℂ → ℝ) (hchi : ContDiff ℝ 2 chi)
    (hc : HasCompactSupport chi) (hchi0 : ∀ x, 0 ≤ chi x)
    (hsupp : tsupport chi ⊆ Bᶜ) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x ∈ Bᶜ,
      closedComplementLogGain A B hA hB hAB hab ha hb x ≤ M) :
    (∫⁻ x : ℂ, ENNReal.ofReal (chi x *
      max ((closedComplementDensity B hB hab (hAB ha) (hAB hb) x)^2 -
        (closedComplementDensity A hA hab ha hb x)^2) 0)) ≤
      ENNReal.ofReal (M * ∫ x : ℂ, |Δ chi x|) := by
  have h := density_deficit_cutoff (∅ : Finset ℂ) hB.isOpen_compl hM hchi hc
    hchi0 hsupp
    (fun x hx _ => ⟨closedComplementDensity_pos B hB hab (hAB ha) (hAB hb) hx,
      closedComplementDensity_contDiffAt B hB hab (hAB ha) (hAB hb) hx⟩)
    (fun x hx _ => ⟨closedComplementDensity_pos A hA hab ha hb (fun h => hx (hAB h)),
      closedComplementDensity_contDiffAt A hA hab ha hb (fun h => hx (hAB h))⟩)
    (fun x hx _ => closedComplementDensity_curvature B hB hab (hAB ha) (hAB hb) hx)
    (fun x hx _ => closedComplementDensity_curvature A hA hab ha hb (fun h => hx (hAB h)))
    (fun x hx _ => by
      change max (closedComplementLogGain A B hA hB hAB hab ha hb x) 0 ≤ M
      rw [max_eq_left (closedComplementLogGain_nonneg A B hA hB hAB hab ha hb hx)]
      exact hbound x hx)
  simpa using h

end AreaDeficit
