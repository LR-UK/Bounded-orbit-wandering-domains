/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.FinitePunctureArea
import BoundedWanderingDomains.CoveringDensityPullback
import BoundedWanderingDomains.AreaCancellation

/-! # Cancellation for finite models and a covering obstacle

The transport and finiteness inputs to area cancellation are proved here
from a finite puncture model and a holomorphic covering. Only the area gain
estimate on the image remains as an explicit analytic input.
-/

open Set Function MeasureTheory
open scoped ENNReal

namespace AreaDeficit

theorem measurable_hyperbolicAreaWeight (A : Set ℂ) (hA : IsClosed A)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A) :
    Measurable (hyperbolicAreaWeight A hA hab ha hb) :=
  ((measurable_closedComplementDensity A hA hab ha hb).pow_const 2).ennreal_ofReal

/-- On an injective wandering tail, a bound on the area gained by the
target obstacle bounds the area of the first disc in every finite model. -/
theorem finite_model_area_bound
    (P : Finset ℂ) {A : Set ℂ} (hA : IsClosed A) (hPA : (↑P : Set ℂ) ⊆ A)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ P) (hb : b ∈ P)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hcov : IsCoveringMapOn f Aᶜ) (hforward : (↑P : Set ℂ) ⊆ f ⁻¹' A)
    {B W : Set ℂ} (hB : MeasurableSet B) (hW : MeasurableSet W)
    (hBW : B ⊆ W) (hinj : InjOn f W) (himage : f '' W ⊆ W \ B)
    (havoid : ∀ z ∈ W, f z ∉ A) {C : ℝ≥0∞}
    (hgain : (∫⁻ z in f '' W,
      hyperbolicAreaWeight A hA hab (hPA ha) (hPA hb) z -
        hyperbolicAreaWeight (↑P : Set ℂ) P.finite_toSet.isClosed hab ha hb z) ≤ C) :
    (∫⁻ z in B,
      hyperbolicAreaWeight (↑P : Set ℂ) P.finite_toSet.isClosed hab ha hb z) ≤ C := by
  let p := hyperbolicAreaWeight (↑P : Set ℂ) P.finite_toSet.isClosed hab ha hb
  let q := hyperbolicAreaWeight A hA hab (hPA ha) (hPA hb)
  let μ := volume.withDensity p
  let ν := volume.withDensity q
  have hp : Measurable p := measurable_hyperbolicAreaWeight _ _ hab ha hb
  have hi : MeasurableSet (f '' W) :=
    hW.image_of_continuousOn_injOn hf.continuous.continuousOn hinj
  have hfinite : μ W ≠ ∞ := by
    rw [withDensity_apply _ hW]
    exact ne_top_of_le_ne_top
      (finite_puncture_hyperbolicArea_ne_top P
        (Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩) hab ha hb)
      (setLIntegral_le_lintegral _ _)
  have hadvance : μ W ≤ ν (f '' W) + 0 := by
    rw [add_zero, withDensity_apply _ hW, withDensity_apply _ hi]
    exact hyperbolicArea_le_image_of_covering P.finite_toSet.isClosed hA hPA
      hab ha hb hf hcov hforward hW hinj havoid
  have hcost : ν (f '' W) ≤ μ (f '' W) + C := by
    rw [withDensity_apply _ hi, withDensity_apply _ hi]
    calc
      (∫⁻ z in f '' W, q z) ≤ ∫⁻ z in f '' W, p z + (q z - p z) :=
        lintegral_mono (fun _ => le_add_tsub)
      _ = (∫⁻ z in f '' W, p z) + ∫⁻ z in f '' W, q z - p z :=
        lintegral_add_left hp _
      _ ≤ (∫⁻ z in f '' W, p z) + C := add_le_add le_rfl hgain
  have h := finite_area_cancellation hB hBW hfinite himage hadvance hcost
  simpa only [add_zero, μ, withDensity_apply _ hB] using h

end AreaDeficit

#print axioms AreaDeficit.finite_model_area_bound
