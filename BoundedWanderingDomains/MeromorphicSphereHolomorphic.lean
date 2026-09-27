/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import FunctionTheory.Meromorphic.Sphere
import NoWanderingDomains.Sphere.SphereHolomorphic
import BoundedWanderingDomains.SphereHolomorphicManifold

/-! # Normal meromorphic functions as holomorphic sphere-valued maps -/

open Set Filter OnePoint
open scoped Topology Manifold

namespace FunctionTheory

/-- The genuine sphere-valued map associated to a normal meromorphic
representative is holomorphic in sphere charts, including at its poles. -/
theorem MeromorphicNFOn.sphereHolomorphicOn_meromorphicSphereValue
    {f : ℂ → ℂ} (hf : MeromorphicNFOn f Set.univ) :
    NoWanderingDomains.SphereHolomorphicOn (meromorphicSphereValue f) Set.univ := by
  intro a _
  by_cases ha : AnalyticAt ℂ f a
  · let V : Set ℂ := {z | AnalyticAt ℂ f z}
    have hVo : IsOpen V := isOpen_analyticAt ℂ f
    refine ⟨V, hVo, ha, (fun _ _ => mem_univ _), Or.inl ⟨?_, ?_⟩⟩
    · intro z hz
      rw [meromorphicSphereValue_of_analytic hz]
      exact OnePoint.coe_ne_infty _
    · have hd : DifferentiableOn ℂ f V :=
        fun w hw => hw.differentiableAt.differentiableWithinAt
      apply hd.congr
      intro w hw
      rw [meromorphicSphereValue_of_analytic hw]
      simp [NoWanderingDomains.chartFiniteMap]
  · have hnf := hf (mem_univ a)
    have hpole := (meromorphicNFAt_iff_analyticAt_or.mp hnf).resolve_left ha
    have hinv : AnalyticAt ℂ f⁻¹ a := by
      apply hnf.inv.meromorphicOrderAt_nonneg_iff_analyticAt.mp
      rw [meromorphicOrderAt_inv]
      lift meromorphicOrderAt f a to ℤ using hpole.2.1.ne_top with k hk
      norm_cast at hpole ⊢
      omega
    have hnonzero : ∀ᶠ z in 𝓝[≠] a, f z ≠ 0 :=
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hnf.meromorphicAt).mp
        hpole.2.1.ne_top
    have hanalytic : ∀ᶠ z in 𝓝[≠] a, AnalyticAt ℂ f z :=
      hnf.meromorphicAt.eventually_analyticAt
    have hnear : ∀ᶠ z in 𝓝 a, z = a ∨ (AnalyticAt ℂ f z ∧ f z ≠ 0) := by
      filter_upwards [eventually_nhdsWithin_iff.mp hnonzero,
        eventually_nhdsWithin_iff.mp hanalytic] with z hz0 hza
      by_cases h : z = a
      · exact Or.inl h
      · exact Or.inr ⟨hza h,hz0 h⟩
    obtain ⟨V, hV, hVo, haV⟩ := eventually_nhds_iff.mp hnear
    let W : Set ℂ := V ∩ {z | AnalyticAt ℂ f⁻¹ z}
    have hWo : IsOpen W := hVo.inter (isOpen_analyticAt ℂ f⁻¹)
    have haW : a ∈ W := ⟨haV,hinv⟩
    refine ⟨W, hWo, haW, (fun _ _ => mem_univ _), Or.inr ⟨?_, ?_⟩⟩
    · intro z hz
      rcases hV z hz.1 with rfl | ⟨hzA,hz0⟩
      · rw [meromorphicSphereValue_of_not_analytic ha]
        exact OnePoint.infty_ne_coe 0
      · rw [meromorphicSphereValue_of_analytic hzA]
        exact fun h => hz0 (OnePoint.coe_eq_coe.mp h)
    · have hd : DifferentiableOn ℂ (fun z => (f z)⁻¹) W :=
        fun z hz => hz.2.differentiableAt.differentiableWithinAt
      apply hd.congr
      intro z hz
      rcases hV z hz.1 with rfl | ⟨hzA,hz0⟩
      · rw [meromorphicSphereValue_of_not_analytic ha]
        exact (inv_eq_zero.mpr hpole.2.2).symm
      · rw [meromorphicSphereValue_of_analytic hzA]
        rfl

/-- The honest sphere-valued realization of a normal meromorphic function is
holomorphic in the intrinsic manifold sense. -/
theorem MeromorphicNFOn.mdifferentiable_meromorphicSphereValue
    {f : ℂ → ℂ} (hf : MeromorphicNFOn f Set.univ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (meromorphicSphereValue f) := by
  rw [← mdifferentiableOn_univ]
  exact (MeromorphicNFOn.sphereHolomorphicOn_meromorphicSphereValue hf).mdifferentiableOn

end FunctionTheory
