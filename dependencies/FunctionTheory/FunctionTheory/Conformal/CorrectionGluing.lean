import TauCeti.Analysis.Complex.Conformal.Inverse.Function
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Unique nearby preimages glue to a holomorphic, injective correction.
The hypotheses explicitly provide the root existence and uniform injectivity
estimates; the theorem performs the analytic gluing and fixes interpolated points. -/
theorem exists_conformal_correction_of_uniform_local_injectivity
    {U V : Set ℂ} (hV : IsOpen V) {φ g : ℂ → ℂ}
    (hφ : AnalyticOnNhd ℂ φ V) (hg : AnalyticOnNhd ℂ g U)
    {r : ℝ} (hr : 0 < r)
    (htube : ∀ a ∈ V, ball a r ⊆ U)
    (hgi : ∀ a ∈ V, InjOn g (ball a r))
    (hφi : ∀ a ∈ V, InjOn φ (V ∩ ball a r))
    (hroot : ∀ a ∈ V, ∃ w : ℂ, dist w a < r / 2 ∧ g w = φ a) :
    ∃ θ : ℂ → ℂ, AnalyticOnNhd ℂ θ V ∧ InjOn θ V ∧ MapsTo θ V U ∧
      (∀ a ∈ V, dist (θ a) a < r / 2 ∧ g (θ a) = φ a) ∧
      (∀ a ∈ V, g a = φ a → θ a = a) := by
  classical
  let θ : ℂ → ℂ := fun a => if ha : a ∈ V then (hroot a ha).choose else a
  have hθ : ∀ a ∈ V, dist (θ a) a < r / 2 ∧ g (θ a) = φ a := by
    intro a ha
    simpa only [θ, dite_eq_left ha] using (hroot a ha).choose_spec
  have hθball : ∀ a ∈ V, θ a ∈ ball a r :=
    fun a ha => ((hθ a ha).1.trans (half_lt_self hr))
  have hθU : MapsTo θ V U := fun a ha => htube a ha (hθball a ha)
  have hθA : AnalyticOnNhd ℂ θ V := by
    intro a ha
    have hga : AnalyticAt ℂ g (θ a) := hg _ (hθU ha)
    have hgd : deriv g (θ a) ≠ 0 := TauCeti.deriv_ne_zero_of_injOn
      (hg.differentiableOn.mono (htube a ha)) isOpen_ball (hgi a ha) (hθball a ha)
    let q := hga.hasStrictDerivAt.localInverse g (deriv g (θ a)) (θ a) hgd
    have hleft : (q ∘ g) =ᶠ[𝓝 (θ a)] id := hga.hasStrictDerivAt.eventually_left_inverse hgd
    have hqa : q (φ a) = θ a := by
      rw [← (hθ a ha).2]
      exact hleft.eq_of_nhds
    have hqA : AnalyticAt ℂ q (φ a) := by
      rw [← (hθ a ha).2]
      exact hga.analyticAt_localInverse hgd
    have hcomp : AnalyticAt ℂ (q ∘ φ) a := hqA.comp (hφ a ha)
    have hqball : ∀ᶠ b in 𝓝 a, q (φ b) ∈ ball a r :=
      hcomp.continuousAt.tendsto.eventually (isOpen_ball.mem_nhds (by
        simpa only [Function.comp_apply, hqa] using hθball a ha))
    have hright : ∀ᶠ w in 𝓝 (φ a), g (q w) = w := by
      simpa only [(hθ a ha).2] using hga.hasStrictDerivAt.eventually_right_inverse hgd
    have hqeq : ∀ᶠ b in 𝓝 a, g (q (φ b)) = φ b :=
      (hφ a ha).continuousAt.tendsto.eventually hright
    have heq : θ =ᶠ[𝓝 a] q ∘ φ := by
      filter_upwards [hV.mem_nhds ha, ball_mem_nhds a (half_pos hr), hqball, hqeq]
        with b hbV hba hqb hqgb
      apply hgi a ha _ hqb
      · exact ((hθ b hbV).2).trans hqgb.symm
      · exact (dist_triangle (θ b) b a).trans_lt (by
          have h₁ := (hθ b hbV).1
          have h₂ := mem_ball.mp hba
          linarith)
    exact hcomp.congr heq.symm
  have hθi : InjOn θ V := by
    intro x hx y hy hxy
    have hyball : y ∈ ball x r := by
      have h₁ : dist y (θ x) < r / 2 := by
        simpa only [hxy, dist_comm] using (hθ y hy).1
      have h₂ := (hθ x hx).1
      exact (dist_triangle y (θ x) x).trans_lt (by linarith)
    apply hφi x hx ⟨hx, mem_ball_self hr⟩ ⟨hy, hyball⟩
    exact (hθ x hx).2.symm.trans ((congrArg g hxy).trans (hθ y hy).2)
  refine ⟨θ, hθA, hθi, hθU, hθ, ?_⟩
  intro a ha hag
  exact hgi a ha (hθball a ha) (mem_ball_self hr) ((hθ a ha).2.trans hag.symm)

end FunctionTheory
