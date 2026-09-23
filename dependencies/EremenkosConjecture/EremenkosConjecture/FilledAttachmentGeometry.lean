import ComplexApproximation.Topology.FillingStraightChannels
import EremenkosConjecture.RayGeometry
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

open Set Metric Complex

namespace EremenkosConjecture

/-- A compact decoration, a narrow connecting halfstrip, and the fixed wider
halfstrip. Filling this union removes bounded holes without opening the neck. -/
def attachedHalfStrips (C : Set ℂ) (ζ a : ℂ) (s η H : ℝ) : Set ℂ :=
  C ∪ closedHalfStrip ζ s η ∪ closedHalfStrip a 0 H

theorem interior_filled_attachment_gate_bound
    {C : Set ℂ} {ζ a : ℂ} {s η H A : ℝ}
    (hC : ∀ z ∈ C, z.re ≤ A) (hAa : A < a.re) (him : ζ.im = a.im) :
    ∀ z ∈ interior (ComplexApproximation.fill (attachedHalfStrips C ζ a s η H)),
      z.re = a.re → dist z a ≤ η := by
  have hchannel : ∀ z ∈ attachedHalfStrips C ζ a s η H,
      A < z.re → z.re < a.re → |z.im - a.im| ≤ η := by
    intro z hz hzA hza
    rcases hz with (hzC | hzS) | hzH
    · exact False.elim ((not_lt_of_ge (hC z hzC)) hzA)
    · simpa only [him] using hzS.2
    · have hre : a.re ≤ z.re := by simpa only [sub_zero] using hzH.1
      exact False.elim ((not_lt_of_ge hre) hza)
  intro z hz hza
  have hb := ComplexApproximation.interior_fill_gate_bound hAa hchannel z hz hza
  have heq : z - a = ((z.im - a.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hza]
  simpa only [dist_eq_norm, heq, norm_mul, norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs] using hb

theorem right_semicircle_subset_interior_filled_attachment
    (C : Set ℂ) (ζ a : ℂ) (s η : ℝ) {H ρ : ℝ} (hρ : 0 < ρ) (hρH : ρ < H) :
    ∀ θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2),
      circleMap a ρ θ ∈ interior (ComplexApproximation.fill (attachedHalfStrips C ζ a s η H)) := by
  let V : Set ℂ := {z | a.re < z.re ∧ |z.im - a.im| < H}
  have hV : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt (Complex.continuous_im.sub continuous_const).abs continuous_const)
  have hsub : V ⊆ ComplexApproximation.fill (attachedHalfStrips C ζ a s η H) := by
    intro z hz
    apply ComplexApproximation.subset_fill
    exact Or.inr ⟨by simpa using hz.1.le, hz.2.le⟩
  intro θ hθ
  apply (interior_mono hsub)
  rw [hV.interior_eq]
  constructor
  · have hcos := Real.cos_pos_of_mem_Ioo hθ
    have hre : (circleMap a ρ θ).re = a.re + ρ * Real.cos θ := by simp [circleMap]
    rw [hre]
    exact lt_add_of_pos_right _ (mul_pos hρ hcos)
  · have h := Complex.abs_im_le_norm (circleMap a ρ θ - a)
    rw [sub_im, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hρ] at h
    exact h.trans_lt hρH

theorem decoration_subset_interior_filled_attachment
    {X C : Set ℂ} (hXC : X ⊆ interior C) (ζ a : ℂ) (s η H : ℝ) :
    X ⊆ interior (ComplexApproximation.fill (attachedHalfStrips C ζ a s η H)) :=
  hXC.trans (interior_mono (fun _ hz => ComplexApproximation.subset_fill _ (Or.inl (Or.inl hz))))

theorem ray_subset_interior_filled_attachment
    (C : Set ℂ) (ζ a : ℂ) {s η : ℝ} (hs : 0 < s) (hη : 0 < η) (H : ℝ) :
    horizontalRay ζ ⊆ interior (ComplexApproximation.fill (attachedHalfStrips C ζ a s η H)) :=
  (horizontalRay_subset_interior_halfStrip hs hη).trans
    (interior_mono (fun _ hz => ComplexApproximation.subset_fill _ (Or.inl (Or.inr hz))))

end EremenkosConjecture
