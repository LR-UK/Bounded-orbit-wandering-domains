import Runge.CauchyKernel
import Runge.UniformOperations
import Runge.CauchyGreen
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Complex Polynomial MeasureTheory Set

namespace Runge

noncomputable def simpleKernel (K : Set ℂ) (a : ℂ) (ha : a ∉ K) : C(K, ℂ) :=
  ⟨fun z => (a-(z : ℂ))⁻¹,
    (continuous_const.sub continuous_subtype_val).inv₀
      (fun z => sub_ne_zero.mpr (fun h => ha (by
        change a = (z : ℂ) at h
        exact h.symm ▸ z.property)))⟩

theorem simpleKernel_mem (K : Set ℂ) (a : ℂ) (ha : a ∉ K) :
    simpleKernel K a ha ∈ rationalAlgebra K := by
  refine ⟨1, C a - X, ?_, ?_⟩
  · intro z
    simpa using sub_ne_zero.mpr (fun h : a = (z : ℂ) => ha (h.symm ▸ z.property))
  · intro z
    simp [simpleKernel, one_div]

theorem continuous_simpleKernel_along (K : Set ℂ) (γ : ℝ → ℂ)
    (hγ : Continuous γ) (ha : ∀ t, γ t ∉ K) :
    Continuous (fun t => simpleKernel K (γ t) (ha t)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply Continuous.inv₀ ((hγ.comp continuous_fst).sub
    (continuous_subtype_val.comp continuous_snd))
  intro p
  exact sub_ne_zero.mpr (fun h => ha p.1 (by
    change γ p.1 = (p.2 : ℂ) at h
    exact h.symm ▸ p.2.property))

noncomputable def lineCauchyTransform (K : Set ℂ) [CompactSpace K]
    (γ : ℝ → ℂ) (ha : ∀ t, γ t ∉ K) (u v : ℝ) : C(K, ℂ) :=
  ∫ t in u..v, simpleKernel K (γ t) (ha t)

theorem lineCauchyTransform_mem (K : Set ℂ) [CompactSpace K]
    (γ : ℝ → ℂ) (ha : ∀ t, γ t ∉ K) (u v : ℝ) :
    lineCauchyTransform K γ ha u v ∈ rationalClosure K :=
  intervalIntegral_mem_rationalClosure K _
    (fun t => (rationalAlgebra K).le_topologicalClosure (simpleKernel_mem K (γ t) (ha t))) u v

theorem lineCauchyTransform_apply (K : Set ℂ) [CompactSpace K]
    (γ : ℝ → ℂ) (hγ : Continuous γ) (ha : ∀ t, γ t ∉ K) (u v : ℝ) (z : K) :
    lineCauchyTransform K γ ha u v z = ∫ t in u..v, (γ t - (z : ℂ))⁻¹ :=
  continuousMap_intervalIntegral_apply K _ u v
    ((continuous_simpleKernel_along K γ hγ ha).intervalIntegrable u v) z

theorem bottom_line_avoids {K : Set ℂ} {a b : ℂ}
    (hK : K ⊆ Ioo a.re b.re ×ℂ Ioo a.im b.im) (t : ℝ) : (t : ℂ) + a.im * I ∉ K := by
  intro ht
  simpa using (hK ht).2.1

theorem top_line_avoids {K : Set ℂ} {a b : ℂ}
    (hK : K ⊆ Ioo a.re b.re ×ℂ Ioo a.im b.im) (t : ℝ) : (t : ℂ) + b.im * I ∉ K := by
  intro ht
  simpa using (hK ht).2.2

theorem right_line_avoids {K : Set ℂ} {a b : ℂ}
    (hK : K ⊆ Ioo a.re b.re ×ℂ Ioo a.im b.im) (t : ℝ) : (b.re : ℂ) + t * I ∉ K := by
  intro ht
  simpa using (hK ht).1.2

theorem left_line_avoids {K : Set ℂ} {a b : ℂ}
    (hK : K ⊆ Ioo a.re b.re ×ℂ Ioo a.im b.im) (t : ℝ) : (a.re : ℂ) + t * I ∉ K := by
  intro ht
  simpa using (hK ht).1.1

noncomputable def boundaryCauchyTransform (K : Set ℂ) [CompactSpace K] (a b : ℂ)
    (hK : K ⊆ Ioo a.re b.re ×ℂ Ioo a.im b.im) : C(K, ℂ) :=
  lineCauchyTransform K (fun t => t + a.im * I) (bottom_line_avoids hK) a.re b.re -
    lineCauchyTransform K (fun t => t + b.im * I) (top_line_avoids hK) a.re b.re +
    I • lineCauchyTransform K (fun t => b.re + t * I) (right_line_avoids hK) a.im b.im -
    I • lineCauchyTransform K (fun t => a.re + t * I) (left_line_avoids hK) a.im b.im

theorem boundaryCauchyTransform_mem (K : Set ℂ) [CompactSpace K] (a b : ℂ)
    (hK : K ⊆ Ioo a.re b.re ×ℂ Ioo a.im b.im) :
    boundaryCauchyTransform K a b hK ∈ rationalClosure K := by
  exact (rationalClosure K).sub_mem
    ((rationalClosure K).add_mem
      ((rationalClosure K).sub_mem (lineCauchyTransform_mem K _ _ _ _)
        (lineCauchyTransform_mem K _ _ _ _))
      ((rationalClosure K).smul_mem (lineCauchyTransform_mem K _ _ _ _) I))
    ((rationalClosure K).smul_mem (lineCauchyTransform_mem K _ _ _ _) I)

theorem boundaryCauchyTransform_apply (K : Set ℂ) [CompactSpace K] (a b : ℂ)
    (hK : K ⊆ Ioo a.re b.re ×ℂ Ioo a.im b.im) (z : K) :
    boundaryCauchyTransform K a b hK z =
      rectangleBoundary (fun w => (w - (z : ℂ))⁻¹) a b := by
  simp only [boundaryCauchyTransform, ContinuousMap.sub_apply, ContinuousMap.add_apply,
    ContinuousMap.smul_apply, smul_eq_mul, rectangleBoundary]
  rw [lineCauchyTransform_apply K (fun t : ℝ => t + a.im * I) (by fun_prop),
    lineCauchyTransform_apply K (fun t : ℝ => t + b.im * I) (by fun_prop),
    lineCauchyTransform_apply K (fun t : ℝ => b.re + t * I) (by fun_prop),
    lineCauchyTransform_apply K (fun t : ℝ => a.re + t * I) (by fun_prop)]

noncomputable def areaCauchyTransform (K : Set ℂ) [CompactSpace K]
    (c : ℂ → ℂ) (hc : Continuous c) (hsep : Disjoint (tsupport c) K) (a b : ℂ) : C(K, ℂ) :=
  ∫ x : ℝ in a.re..b.re, ∫ y : ℝ in a.im..b.im,
    cauchyKernelFamily K c hc hsep (x + y * I)

theorem areaCauchyTransform_mem (K : Set ℂ) [CompactSpace K]
    (c : ℂ → ℂ) (hc : Continuous c) (hsep : Disjoint (tsupport c) K) (a b : ℂ) :
    areaCauchyTransform K c hc hsep a b ∈ rationalClosure K := by
  apply intervalIntegral_mem_rationalClosure
  intro x
  apply intervalIntegral_mem_rationalClosure
  intro y
  exact (rationalAlgebra K).le_topologicalClosure (cauchyKernelFamily_mem K c hc hsep _)

theorem areaCauchyTransform_apply (K : Set ℂ) [CompactSpace K]
    (c : ℂ → ℂ) (hc : Continuous c) (hsep : Disjoint (tsupport c) K) (a b : ℂ) (z : K) :
    areaCauchyTransform K c hc hsep a b z =
      ∫ x : ℝ in a.re..b.re, ∫ y : ℝ in a.im..b.im,
        c (x + y * I) / (x + y * I - (z : ℂ)) := by
  have hjoint : Continuous (fun p : ℝ × ℝ => cauchyKernelFamily K c hc hsep (p.1 + p.2 * I)) :=
    (continuous_cauchyKernelFamily K c hc hsep).comp (by fun_prop)
  have hinner : Continuous (fun x : ℝ => ∫ y : ℝ in a.im..b.im,
      cauchyKernelFamily K c hc hsep (x + y * I)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hjoint _ _
  rw [areaCauchyTransform, continuousMap_intervalIntegral_apply K _ _ _
    (hinner.intervalIntegrable _ _) z]
  apply intervalIntegral.integral_congr
  intro x _
  exact continuousMap_intervalIntegral_apply K _ _ _
    ((hjoint.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _) z

end Runge
