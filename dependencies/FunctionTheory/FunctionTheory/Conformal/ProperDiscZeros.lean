import FunctionTheory.Conformal.ProperDiscBoundary
import Mathlib.Analysis.Meromorphic.FactorizedRational

open Set Metric Filter Function
open scoped Topology BigOperators
namespace FunctionTheory
set_option autoImplicit false

/-- A proper holomorphic disc map has finite order at every point.
Properness itself excludes the identically zero map. -/
theorem order_ne_top_of_isProperMap_holomorphic_disc
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball (0:ℂ) 1))
    (hmap : MapsTo f (ball (0:ℂ) 1) (ball (0:ℂ) 1))
    (hproper : IsProperMap (fun z : ball (0:ℂ) 1 =>
      (⟨f z,hmap z.property⟩ : ball (0:ℂ) 1))) :
    ∀ z∈ball (0:ℂ) 1, meromorphicOrderAt f z≠⊤ := by
  let F : ball (0:ℂ) 1 → ball (0:ℂ) 1 := fun z => ⟨f z,hmap z.property⟩
  obtain ⟨s,hs0,hs1,hlarge⟩ := exists_boundary_collar_of_isProperMap_disc F hproper zero_lt_one
  let z₀ : ℂ := (((s+1)/2:ℝ):ℂ)
  have hn₀ : ‖z₀‖=(s+1)/2 := by
    simp only [z₀,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : (s+1)/2>0)]
  have hz₀ : z₀∈ball (0:ℂ) 1 := by rw [mem_ball_zero_iff,hn₀]; linarith
  have hfn : f z₀≠0 := by
    apply norm_pos_iff.mp
    exact hlarge ⟨z₀,hz₀⟩ (by rw [hn₀]; linarith)
  have ho₀ : meromorphicOrderAt f z₀≠⊤ := by
    rw [(hf z₀ hz₀).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hfn]
    exact WithTop.coe_ne_top
  intro z hz
  exact hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    (convex_ball (0:ℂ) 1).isPreconnected hz₀ hz ho₀

/-- The divisor of a proper holomorphic disc map has finite support. -/
theorem finite_divisor_support_of_isProperMap_holomorphic_disc
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball (0:ℂ) 1))
    (hmap : MapsTo f (ball (0:ℂ) 1) (ball (0:ℂ) 1))
    (hproper : IsProperMap (fun z : ball (0:ℂ) 1 =>
      (⟨f z,hmap z.property⟩ : ball (0:ℂ) 1))) :
    (MeromorphicOn.divisor f (ball (0:ℂ) 1)).support.Finite := by
  have ho := order_ne_top_of_isProperMap_holomorphic_disc hf hmap hproper
  change (Function.support (MeromorphicOn.divisor f (ball (0:ℂ) 1) : ℂ → ℤ)).Finite
  rw [← hf.meromorphicNFOn.zero_set_eq_divisor_support (fun z => ho z z.property)]
  exact finite_fibre_of_isProperMap_holomorphic_disc hf hmap hproper (by simp : ‖(0:ℂ)‖<1)

/-- Extract all zeros of a proper holomorphic disc map using Mathlib's
finite-divisor factorisation. The remaining factor is analytic and nowhere
zero on the whole open disc; equality holds at the zeros as well. -/
theorem exists_zero_factorisation_of_isProperMap_holomorphic_disc
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball (0:ℂ) 1))
    (hmap : MapsTo f (ball (0:ℂ) 1) (ball (0:ℂ) 1))
    (hproper : IsProperMap (fun z : ball (0:ℂ) 1 =>
      (⟨f z,hmap z.property⟩ : ball (0:ℂ) 1))) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball (0:ℂ) 1) ∧
      (∀ z∈ball (0:ℂ) 1, g z≠0) ∧
      EqOn f ((∏ᶠ u : ℂ, (·-u)^MeromorphicOn.divisor f (ball (0:ℂ) 1) u) • g)
        (ball (0:ℂ) 1) := by
  have ho := order_ne_top_of_isProperMap_holomorphic_disc hf hmap hproper
  have hfin := finite_divisor_support_of_isProperMap_holomorphic_disc hf hmap hproper
  obtain ⟨g,hg,hgn,heq⟩ := hf.meromorphicOn.extract_zeros_poles
    (fun z => ho z z.property) hfin
  refine ⟨g,hg,fun z hz => hgn ⟨z,hz⟩,?_⟩
  have hP : AnalyticOnNhd ℂ
      (∏ᶠ u : ℂ, (·-u)^MeromorphicOn.divisor f (ball (0:ℂ) 1) u) (ball (0:ℂ) 1) :=
    fun z hz => Function.FactorizedRational.analyticAt (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf z)
  have hprod := hP.smul hg
  intro z hz
  have hnear := (hf z hz).meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
    (hprod z hz).meromorphicAt hz isOpen_ball.preperfect heq
  exact ((hf z hz).meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hprod z hz).meromorphicNFAt).mp hnear |>.eq_of_nhds

end FunctionTheory
