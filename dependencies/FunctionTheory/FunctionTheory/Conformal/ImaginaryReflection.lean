import TauCeti.Analysis.Complex.Conformal.Reflection.Principle
import Mathlib.Topology.Algebra.GroupWithZero

/-! # Schwarz reflection across the imaginary axis

This is the public Tau Ceti reflection principle transported by a quarter-turn.
The imaginary axis is the boundary in the exponential coordinate of a strip.
Boundary continuity is an explicit hypothesis, as in the upstream theorem.
-/

open Set Complex
open scoped ComplexConjugate

namespace FunctionTheory

theorem exists_holomorphic_reflection_across_imaginary_axis
    {Ω : Set ℂ} {f : ℂ → ℂ} (hΩo : IsOpen Ω)
    (hΩ : MapsTo (fun z => -conj z) Ω Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.re}))
    (hhol : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.re}))
    (haxis : ∀ z ∈ Ω, z.re = 0 → (f z).re = 0) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Ω ∧
      EqOn F f (Ω ∩ {z : ℂ | 0 ≤ z.re}) ∧
      ∀ z ∈ Ω, F (-conj z) = -conj (F z) := by
  let V : Set ℂ := (fun z => I * z) '' Ω
  let q : ℂ → ℂ := fun w => I * f (-I * w)
  have hcancel (z : ℂ) : -I * (I * z) = z := by simp [← mul_assoc]
  have hre (w : ℂ) : (-I * w).re = w.im := by simp [Complex.mul_re]
  have him (z : ℂ) : (I * z).im = z.re := by simp [Complex.mul_im]
  have hreflect (z : ℂ) : I * (-conj z) = conj (I * z) := by simp
  have hVo : IsOpen V := by
    exact (Homeomorph.mulLeft₀ I I_ne_zero).isOpenMap Ω hΩo
  have hpre : ∀ w ∈ V, -I * w ∈ Ω := by
    rintro w ⟨z, hz, rfl⟩
    simpa only [hcancel] using hz
  have hVs : MapsTo conj V V := by
    rintro w ⟨z, hz, rfl⟩
    exact ⟨-conj z, hΩ hz, hreflect z⟩
  have hmap₀ : MapsTo (fun w => -I * w) (V ∩ {w : ℂ | 0 ≤ w.im})
      (Ω ∩ {z : ℂ | 0 ≤ z.re}) := by
    intro w hw
    exact ⟨hpre w hw.1, by simpa only [mem_ofPred_eq, hre] using hw.2⟩
  have hmap_pos : MapsTo (fun w => -I * w) (V ∩ {w : ℂ | 0 < w.im})
      (Ω ∩ {z : ℂ | 0 < z.re}) := by
    intro w hw
    exact ⟨hpre w hw.1, by simpa only [mem_ofPred_eq, hre] using hw.2⟩
  have hqc : ContinuousOn q (V ∩ {w : ℂ | 0 ≤ w.im}) :=
    continuous_const.continuousOn.mul
      (hcont.comp (continuous_const.mul continuous_id).continuousOn hmap₀)
  have hqh : DifferentiableOn ℂ q (V ∩ {w : ℂ | 0 < w.im}) :=
    (hhol.comp (differentiable_id.const_mul (-I)).differentiableOn hmap_pos).const_mul I
  have hqa : ∀ w ∈ V, w.im = 0 → (q w).im = 0 := by
    intro w hw hw0
    change (I * f (-I * w)).im = 0
    rw [him]
    exact haxis _ (hpre w hw) (by rw [hre, hw0])
  obtain ⟨G, hG, hGq, hGs⟩ :=
    TauCeti.exists_differentiableOn_eqOn_conj_of_symmetric hVo hVs hqc hqh hqa
  refine ⟨fun z => -I * G (I * z), ?_, ?_, ?_⟩
  · exact (hG.comp (differentiable_id.const_mul I).differentiableOn
      (fun z hz => mem_image_of_mem _ hz)).const_mul (-I)
  · intro z hz
    have hIz : I * z ∈ V ∩ {w : ℂ | 0 ≤ w.im} :=
      ⟨mem_image_of_mem _ hz.1, by simpa only [mem_ofPred_eq, him] using hz.2⟩
    change -I * G (I * z) = f z
    rw [hGq hIz]
    change -I * (I * f (-I * (I * z))) = f z
    simp only [hcancel]
  · intro z hz
    change -I * G (I * (-conj z)) = -conj (-I * G (I * z))
    rw [hreflect, hGs _ (mem_image_of_mem _ hz)]
    simp

end FunctionTheory
