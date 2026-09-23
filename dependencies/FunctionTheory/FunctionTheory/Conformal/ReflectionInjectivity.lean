import FunctionTheory.Conformal.ImaginaryReflection
import TauCeti.Analysis.Complex.Conformal.Inverse.Function
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Injectivity across a reflected boundary

For an open map, injectivity over a dense set of target values implies full
injectivity. Applied to Schwarz reflection, the two open halfplanes separate
the branches, and openness also rules out collisions on the boundary itself.
-/

open Set Metric Complex Filter
open scoped ComplexConjugate Topology

namespace FunctionTheory

theorem injOn_of_open_images_of_injOn_dense_preimage
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    {U : Set X} {D : Set Y} {f : X → Y} (hU : IsOpen U)
    (hopen : ∀ V ⊆ U, IsOpen V → IsOpen (f '' V))
    (hD : Dense D) (hinj : InjOn f (U ∩ f ⁻¹' D)) : InjOn f U := by
  intro x hx y hy hxy
  by_contra hne
  obtain ⟨V, W, hV, hW, hxV, hyW, hVW⟩ := t2_separation hne
  have hVo := hopen (V ∩ U) inter_subset_right (hV.inter hU)
  have hWo := hopen (W ∩ U) inter_subset_right (hW.inter hU)
  obtain ⟨v, ⟨hvV, hvW⟩, hvD⟩ := hD.inter_open_nonempty
    (f '' (V ∩ U) ∩ f '' (W ∩ U)) (hVo.inter hWo)
    ⟨f x, ⟨x, ⟨hxV, hx⟩, rfl⟩, ⟨y, ⟨hyW, hy⟩, hxy.symm⟩⟩
  obtain ⟨a, ha, hav⟩ := hvV
  obtain ⟨b, hb, hbv⟩ := hvW
  have hab := hinj ⟨ha.2, show f a ∈ D from hav.symm ▸ hvD⟩
    ⟨hb.2, show f b ∈ D from hbv.symm ▸ hvD⟩ (hav.trans hbv.symm)
  exact disjoint_left.mp hVW ha.1 (hab.symm ▸ hb.1)

theorem dense_re_ne_zero : Dense {z : ℂ | z.re ≠ 0} := by
  apply dense_iff_inter_open.mpr
  intro U hU hUn
  obtain ⟨z, hz⟩ := hUn
  by_cases hre : z.re = 0
  · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z hz
    refine ⟨z + (r / 2 : ℝ), hball ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (half_pos hr)]
      exact half_lt_self hr
    · change (z + (r / 2 : ℝ)).re ≠ 0
      simp only [Complex.add_re, Complex.ofReal_re, hre, zero_add]
      exact (half_pos hr).ne'
  · exact ⟨z, hz, hre⟩

theorem injOn_of_imaginary_reflection {Ω : Set ℂ} {F : ℂ → ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω) (h0 : (0 : ℂ) ∈ Ω)
    (hΩs : MapsTo (fun z => -conj z) Ω Ω) (hF : DifferentiableOn ℂ F Ω)
    (hFs : ∀ z ∈ Ω, F (-conj z) = -conj (F z)) (hF0 : F 0 = 0)
    (hpos : ∀ z ∈ Ω, 0 < z.re → 0 < (F z).re)
    (hinj : InjOn F (Ω ∩ {z : ℂ | 0 < z.re})) : InjOn F Ω := by
  have haxis : ∀ z ∈ Ω, z.re = 0 → (F z).re = 0 := by
    intro z hz hz0
    have he : -conj z = z := by apply Complex.ext <;> simp [hz0]
    have H := congrArg Complex.re (hFs z hz)
    rw [he] at H
    simp only [Complex.neg_re, Complex.conj_re] at H
    linarith
  have hneg : ∀ z ∈ Ω, z.re < 0 → (F z).re < 0 := by
    intro z hz hzneg
    have H := hpos (-conj z) (hΩs hz) (by simpa using neg_pos.mpr hzneg)
    rw [hFs z hz] at H
    simpa using H
  have hopen : ∀ V ⊆ Ω, IsOpen V → IsOpen (F '' V) := by
    rcases (hF.analyticOnNhd hΩo).is_constant_or_isOpen hΩc with hc | ho
    · obtain ⟨c, hc⟩ := hc
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩo 0 h0
      have hx : ((r / 2 : ℝ) : ℂ) ∈ Ω := hball (by
        simpa only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (half_pos hr)] using half_lt_self hr)
      have H := hpos _ hx (by simpa using half_pos hr)
      rw [hc _ hx, ← hc 0 h0, hF0] at H
      norm_num at H
    · exact ho
  apply injOn_of_open_images_of_injOn_dense_preimage hΩo hopen dense_re_ne_zero
  intro z hz w hw hzw
  have hz0 : z.re ≠ 0 := fun he => hz.2 (haxis z hz.1 he)
  have hw0 : w.re ≠ 0 := fun he => hw.2 (haxis w hw.1 he)
  by_cases hzpos : 0 < z.re
  · by_cases hwpos : 0 < w.re
    · exact hinj ⟨hz.1, hzpos⟩ ⟨hw.1, hwpos⟩ hzw
    · have hwneg : w.re < 0 := lt_of_le_of_ne (le_of_not_gt hwpos) hw0
      have H := congrArg Complex.re hzw
      linarith [hpos z hz.1 hzpos, hneg w hw.1 hwneg]
  · have hzneg : z.re < 0 := lt_of_le_of_ne (le_of_not_gt hzpos) hz0
    by_cases hwpos : 0 < w.re
    · have H := congrArg Complex.re hzw
      linarith [hneg z hz.1 hzneg, hpos w hw.1 hwpos]
    · have hwneg : w.re < 0 := lt_of_le_of_ne (le_of_not_gt hwpos) hw0
      have he : F (-conj z) = F (-conj w) := by rw [hFs z hz.1, hFs w hw.1, hzw]
      have hh := hinj ⟨hΩs hz.1, by simpa using neg_pos.mpr hzneg⟩
        ⟨hΩs hw.1, by simpa using neg_pos.mpr hwneg⟩ he
      simpa using congrArg (fun v : ℂ => -conj v) hh

/-- Injectivity is required only on the open original half. The reflected
extension has a simple zero at the origin. Boundary continuity is still a
hypothesis, supplied by the geometric boundary-extension argument. -/
theorem exists_conformal_reflection_at_zero {Ω : Set ℂ} {f : ℂ → ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω) (h0 : (0 : ℂ) ∈ Ω)
    (hΩs : MapsTo (fun z => -conj z) Ω Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.re}))
    (hhol : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.re}))
    (haxis : ∀ z ∈ Ω, z.re = 0 → (f z).re = 0) (hf0 : f 0 = 0)
    (hpos : ∀ z ∈ Ω, 0 < z.re → 0 < (f z).re)
    (hinj : InjOn f (Ω ∩ {z : ℂ | 0 < z.re})) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Ω ∧ InjOn F Ω ∧
      EqOn F f (Ω ∩ {z : ℂ | 0 ≤ z.re}) ∧ F 0 = 0 ∧ deriv F 0 ≠ 0 := by
  obtain ⟨F, hF, hEq, hFs⟩ := exists_holomorphic_reflection_across_imaginary_axis
    hΩo hΩs hcont hhol haxis
  have hF0 : F 0 = 0 := (hEq ⟨h0, by simp⟩).trans hf0
  have hFi := injOn_of_imaginary_reflection hΩo hΩc h0 hΩs hF hFs hF0
    (fun z hz hp => by rw [hEq ⟨hz, hp.le⟩]; exact hpos z hz hp)
    (fun z hz w hw he => hinj hz hw (by
      rwa [hEq ⟨hz.1, (show 0 < z.re from hz.2).le⟩,
        hEq ⟨hw.1, (show 0 < w.re from hw.2).le⟩] at he))
  exact ⟨F, hF, hFi, hEq, hF0, TauCeti.deriv_ne_zero_of_injOn hF hΩo hFi h0⟩

/-- A simple zero at a straight boundary has positive real derivative when
the map carries the right half into the right half and the axis into itself. -/
theorem deriv_positive_real_of_halfplane_map {Ω : Set ℂ} {F : ℂ → ℂ}
    (hΩ : Ω ∈ 𝓝 (0 : ℂ)) (hF : DifferentiableAt ℂ F 0) (hF0 : F 0 = 0)
    (hne : deriv F 0 ≠ 0)
    (haxis : ∀ z ∈ Ω, z.re = 0 → (F z).re = 0)
    (hpos : ∀ z ∈ Ω, 0 < z.re → 0 < (F z).re) :
    ∃ a : ℝ, 0 < a ∧ deriv F 0 = (a : ℂ) := by
  have hi : HasDerivAt (fun z : ℂ => F (I * z)) (deriv F 0 * I) 0 := by
    have hbase : HasDerivAt F (deriv F 0) (I * (0 : ℂ)) := by simpa using hF.hasDerivAt
    have harg : HasDerivAt (fun z : ℂ => I * z) I 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul I
    exact hbase.comp 0 harg
  have hri := hi.real_of_complex
  have hm : ∀ᶠ t : ℝ in 𝓝 0, I * (t : ℂ) ∈ Ω := by
    have hc : Continuous (fun t : ℝ => I * (t : ℂ)) :=
      continuous_const.mul Complex.continuous_ofReal
    have ht : Tendsto (fun t : ℝ => I * (t : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) := by
      simpa using hc.tendsto 0
    exact ht.eventually hΩ
  have heq : (fun t : ℝ => (F (I * (t : ℂ))).re) =ᶠ[𝓝 0] (fun _ => 0) :=
    hm.mono fun t ht => haxis _ ht (by simp)
  have him : (deriv F 0).im = 0 := by
    have H := hri.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq heq)
    simpa [Complex.mul_re] using H
  have hr := hF.hasDerivAt.real_of_complex
  have hlim := hr.tendsto_slope_zero_right
  have hmreal : ∀ᶠ t : ℝ in 𝓝[>] 0, (t : ℂ) ∈ Ω := by
    exact ((Complex.continuous_ofReal.tendsto 0).eventually (by simpa using hΩ)).filter_mono
      nhdsWithin_le_nhds
  have hnonneg : 0 ≤ (deriv F 0).re := by
    apply ge_of_tendsto hlim
    filter_upwards [hmreal, self_mem_nhdsWithin] with t ht htpos
    have hp : 0 < (F (t : ℂ)).re := hpos _ ht (by exact htpos)
    simpa [hF0, smul_eq_mul] using mul_nonneg (inv_nonneg.mpr (le_of_lt htpos)) hp.le
  have hreal : deriv F 0 = ((deriv F 0).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  refine ⟨(deriv F 0).re, lt_of_le_of_ne hnonneg ?_, hreal⟩
  intro he
  apply hne
  rw [hreal, ← he, Complex.ofReal_zero]

theorem exists_positive_conformal_reflection_at_zero {Ω : Set ℂ} {f : ℂ → ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω) (h0 : (0 : ℂ) ∈ Ω)
    (hΩs : MapsTo (fun z => -conj z) Ω Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.re}))
    (hhol : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.re}))
    (haxis : ∀ z ∈ Ω, z.re = 0 → (f z).re = 0) (hf0 : f 0 = 0)
    (hpos : ∀ z ∈ Ω, 0 < z.re → 0 < (f z).re)
    (hinj : InjOn f (Ω ∩ {z : ℂ | 0 < z.re})) :
    ∃ (F : ℂ → ℂ) (a : ℝ), DifferentiableOn ℂ F Ω ∧ InjOn F Ω ∧
      EqOn F f (Ω ∩ {z : ℂ | 0 ≤ z.re}) ∧ F 0 = 0 ∧ 0 < a ∧ deriv F 0 = (a : ℂ) := by
  obtain ⟨F, hF, hFi, hEq, hF0, hne⟩ := exists_conformal_reflection_at_zero
    hΩo hΩc h0 hΩs hcont hhol haxis hf0 hpos hinj
  obtain ⟨a, ha, hda⟩ := deriv_positive_real_of_halfplane_map (hΩo.mem_nhds h0)
    (hF.differentiableAt (hΩo.mem_nhds h0)) hF0 hne
    (fun z hz hz0 => by
      rw [hEq ⟨hz, show 0 ≤ z.re by rw [hz0]⟩]
      exact haxis z hz hz0)
    (fun z hz hp => by rw [hEq ⟨hz, hp.le⟩]; exact hpos z hz hp)
  exact ⟨F, a, hF, hFi, hEq, hF0, ha, hda⟩

end FunctionTheory
