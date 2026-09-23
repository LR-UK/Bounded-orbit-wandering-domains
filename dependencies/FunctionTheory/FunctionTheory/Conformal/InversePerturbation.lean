import FunctionTheory.Analytic.UniformPreimageStability
import Mathlib.Analysis.Analytic.Order

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- A conformal change of target preserves the centered local degree. -/
theorem analyticOrderAt_centered_postcomp_of_deriv_ne_zero
    {f h : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a)
    (hh : AnalyticAt ℂ h (f a)) (hhd : deriv h (f a) ≠ 0) :
    analyticOrderAt (fun z => h (f z) - h (f a)) a =
      analyticOrderAt (fun z => f z - f a) a := by
  have hH : AnalyticAt ℂ (fun w => h w - h (f a)) (f a) := hh.sub analyticAt_const
  have H := hH.analyticOrderAt_comp hf
  rw [hh.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hhd, one_mul] at H
  exact H

/-- A holomorphic embedding sufficiently close to the identity covers a
uniform neighbourhood of a compact set. Its inverse at a nearby target
remains close to the original base point. This supplies the domain and
error bounds needed when transporting a finite-chain perturbation backwards. -/
theorem exists_uniform_inverse_tolerance_near_compact
    {V K : Set ℂ} (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ θ : ℂ → ℂ, AnalyticOnNhd ℂ θ V → InjOn θ V →
      (∀ z ∈ V, ‖θ z - z‖ < δ) →
      ∀ a ∈ K, ∀ v : ℂ, ‖v - a‖ < δ →
        v ∈ θ '' V ∧ dist (Function.invFunOn θ V v) a < ε := by
  have hnc : ∀ a ∈ K, ¬ ∀ᶠ z in 𝓝 a, (fun w : ℂ => w) z = a := by
    intro a _ hconst
    have heq : (fun w : ℂ => w) =ᶠ[𝓝 a] (fun _ => a) := hconst
    have hd := heq.deriv_eq
    norm_num at hd
  obtain ⟨δ, hδ, H⟩ := exists_uniform_stable_local_image hV hK hKV
    (f := fun z => z) analyticOnNhd_id hnc hε
  refine ⟨δ, hδ, ?_⟩
  intro θ hθ hi hnear a ha v hv
  obtain ⟨w, hw, hθw⟩ := H θ hθ
    (fun z hz => by simpa only [norm_sub_rev] using hnear z hz) a ha v hv
  refine ⟨⟨w, hw.1, hθw⟩, ?_⟩
  rw [← hθw, hi.leftInvOn_invFunOn hw.1]
  exact mem_ball.mp hw.2

end FunctionTheory
