import BoundedWanderingDomains.AreaCancellation
import Mathlib.MeasureTheory.Function.Jacobian

open Set Function MeasureTheory Filter
open scoped ENNReal Topology

namespace AreaDeficit

theorem measurable_forwardOrbit {f : ℂ → ℂ} {B : Set ℂ}
    (hB : MeasurableSet B) (hwand : HasDisjointForwardImages f B)
    (hinj : ∀ n, InjOn (f^[n]) B) (hf : ContinuousOn f (forwardOrbit f B)) :
    MeasurableSet (forwardOrbit f B) := by
  have hi := injOn_forwardOrbit hwand hinj
  have hm : ∀ n : ℕ, MeasurableSet (f^[n] '' B) := by
    intro n
    induction n with
    | zero => simpa using hB
    | succ n ih =>
        have hs : f^[n] '' B ⊆ forwardOrbit f B := fun _ hx => mem_iUnion.mpr ⟨n, hx⟩
        simpa only [iterate_succ', image_comp] using
          ih.image_of_continuousOn_injOn (hf.mono hs) (hi.mono hs)
  exact MeasurableSet.iUnion hm

/-- An integrated deficit yields the one-step area comparison. Change of
variables is proved by mathlib's Jacobian theorem, not assumed. Densities
here are area weights; subtraction in ENNReal is the positive deficit. -/
theorem area_advance_of_integrated_defect
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {W : Set ℂ}
    {a b : ℂ → ℝ≥0∞} {C : ℝ≥0∞}
    (hW : MeasurableSet W)
    (hdf : ∀ x ∈ W, HasFDerivWithinAt f (df x) W x)
    (hinj : InjOn f W) (hb : Measurable b)
    (hdef : (∫⁻ x in W, a x - ENNReal.ofReal |(df x).det| * b (f x)) ≤ C) :
    volume.withDensity a W ≤ volume.withDensity b (f '' W) + C := by
  have hc : ContinuousOn f W := fun x hx => (hdf x hx).differentiableWithinAt.continuousWithinAt
  have hj : AEMeasurable (fun x => ENNReal.ofReal |(df x).det| * b (f x))
      (volume.restrict W) :=
    (aemeasurable_ofReal_abs_det_fderivWithin volume hW hdf).mul
      (hb.comp_aemeasurable (hc.aemeasurable hW))
  rw [withDensity_apply _ hW,
    withDensity_apply _ (measurable_image_of_fderivWithin hW hdf hinj),
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hW hdf hinj b]
  calc
    (∫⁻ x in W, a x) ≤ ∫⁻ x in W,
        ENNReal.ofReal |(df x).det| * b (f x) +
          (a x - ENNReal.ofReal |(df x).det| * b (f x)) := by
      apply lintegral_mono
      intro x
      exact le_add_tsub
    _ = (∫⁻ x in W, ENNReal.ofReal |(df x).det| * b (f x)) +
        ∫⁻ x in W, a x - ENNReal.ofReal |(df x).det| * b (f x) :=
      lintegral_add_left' hj _
    _ ≤ (∫⁻ x in W, ENNReal.ofReal |(df x).det| * b (f x)) + C := by gcongr

/-- Cancellation with the analytic transport input reduced to an integral
deficit. The separate puncture-area cost is still an explicit hypothesis. -/
theorem wandering_area_bound_of_integrated_defect
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {B : Set ℂ}
    {a b : ℂ → ℝ≥0∞} {C D : ℝ≥0∞}
    (hB : MeasurableSet B) (hW : MeasurableSet (forwardOrbit f B))
    (hwand : HasDisjointForwardImages f B) (hinj : ∀ n, InjOn (f^[n]) B)
    (hdf : ∀ x ∈ forwardOrbit f B, HasFDerivWithinAt f (df x) (forwardOrbit f B) x)
    (hb : Measurable b) (hfinite : volume.withDensity a (forwardOrbit f B) ≠ ∞)
    (hdef : (∫⁻ x in forwardOrbit f B,
      a x - ENNReal.ofReal |(df x).det| * b (f x)) ≤ C)
    (hcost : volume.withDensity b (f '' forwardOrbit f B) ≤
      volume.withDensity a (f '' forwardOrbit f B) + D) :
    volume.withDensity a B ≤ D + C :=
  wandering_area_bound hB hwand hfinite
    (area_advance_of_integrated_defect hW hdf (injOn_forwardOrbit hwand hinj) hb hdef) hcost

/-- The positive-area contradiction with transport proved by change of
variables. Uniform deficit, puncture cost, and density blowup are the
remaining geometric inputs, all explicitly quantified. -/
theorem null_wandering_set_of_integrated_defects
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {B : Set ℂ}
    {a b : ℕ → ℂ → ℝ≥0∞} {C D : ℝ≥0∞}
    (hB : MeasurableSet B) (hwand : HasDisjointForwardImages f B)
    (hinj : ∀ n, InjOn (f^[n]) B)
    (hdf : ∀ x ∈ forwardOrbit f B, HasFDerivWithinAt f (df x) (forwardOrbit f B) x)
    (hC : C ≠ ∞) (hD : D ≠ ∞)
    (ha : ∀ j, AEMeasurable (a j) (volume.restrict B)) (hb : ∀ j, Measurable (b j))
    (hfinite : ∀ j, volume.withDensity (a j) (forwardOrbit f B) ≠ ∞)
    (hdef : ∀ j, (∫⁻ x in forwardOrbit f B,
      a j x - ENNReal.ofReal |(df x).det| * b j (f x)) ≤ C)
    (hcost : ∀ j, volume.withDensity (b j) (f '' forwardOrbit f B) ≤
      volume.withDensity (a j) (f '' forwardOrbit f B) + D)
    (hlim : ∀ᵐ x ∂volume.restrict B, Tendsto (fun j => a j x) atTop (𝓝 ∞)) :
    volume B = 0 := by
  have hW := measurable_forwardOrbit hB hwand hinj
    (fun x hx => (hdf x hx).differentiableWithinAt.continuousWithinAt)
  exact null_wandering_set_of_density_data hB hwand hC hD ha hfinite
    (fun j => area_advance_of_integrated_defect hW hdf (injOn_forwardOrbit hwand hinj)
      (hb j) (hdef j)) hcost hlim

end AreaDeficit
