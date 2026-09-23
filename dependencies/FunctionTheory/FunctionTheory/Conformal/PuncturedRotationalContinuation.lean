import FunctionTheory.Conformal.RotationalContinuation
import FunctionTheory.Topology.CountableDisc

open Set Filter Function Metric
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- A rotational identity continues across a circle wherever both outer
function evaluations are regular. Countably many singularities may be removed;
no equality of the two regular domains is assumed. -/
theorem eventually_rotation_identity_on_regular_domains
    (θ : ℂ → ℂ) (H : ℕ → ℂ → ℂ) (G : ℕ → Set ℂ) (ρ : ℕ → ℂ)
    {a : ℂ} (ha : ‖a‖=1) {ε : ℝ} (hε : 0<ε)
    (hθ : AnalyticOnNhd ℂ θ (ball 0 1 ∪ ball a ε))
    (hθi : InjOn θ (ball a ε))
    (hG : ∀ n, (G n)ᶜ.Countable)
    (hH : ∀ n, AnalyticOnNhd ℂ (H n) (G n))
    (hdom : ∀ n, MapsTo θ (ball (0:ℂ) 1) (G n))
    (hρ : Tendsto ρ atTop (𝓝 1)) (hnorm : ∀ n, ‖ρ n‖=1)
    (hid : ∀ n, ∀ z∈ball (0:ℂ) 1, H n (θ (ρ n*z))=H n (θ z)) :
    ∀ᶠ n in atTop, ∀ z∈ball a (ε/2),
      θ z∈G n → θ (ρ n*z)∈G n → H n (θ (ρ n*z))=H n (θ z) := by
  have hacl : a∈closure (ball (0:ℂ) 1) := by
    rw [closure_ball _ one_ne_zero]
    simpa only [mem_closedBall,dist_zero_right,ha] using (le_refl (1:ℝ))
  obtain ⟨b,hb,hba⟩ := Metric.mem_closure_iff.mp hacl (ε/2) (half_pos hε)
  have hbB : b∈ball a (ε/2) := by simpa only [mem_ball,dist_comm] using hba
  have hB : ball a (ε/2)⊆ball a ε := ball_subset_ball (by linarith)
  filter_upwards [eventually_rotations_map_collar ρ hρ hnorm a hε] with n hn
  have hρ0 : ρ n≠0 := by intro H; simpa [H] using hnorm n
  have hrotD : MapsTo (fun z => ρ n*z) (ball (0:ℂ) 1) (ball 0 1) := by
    intro z hz
    simpa only [mem_ball,dist_zero_right,norm_mul,hnorm n,one_mul] using hz
  let S : Set ℂ := (ball a (ε/2)∩θ ⁻¹' (G n)ᶜ) ∪
    (ball a (ε/2)∩(fun z => θ (ρ n*z)) ⁻¹' (G n)ᶜ)
  have hS : S.Countable := by
    apply Set.Countable.union
    · exact (show MapsTo θ (ball a (ε/2)∩θ ⁻¹' (G n)ᶜ) (G n)ᶜ from
        fun z hz => hz.2).countable_of_injOn
        (hθi.mono (fun z hz => hB hz.1)) (hG n)
    · apply (show MapsTo (fun z => θ (ρ n*z))
        (ball a (ε/2)∩(fun z => θ (ρ n*z)) ⁻¹' (G n)ᶜ) (G n)ᶜ from
        fun z hz => hz.2).countable_of_injOn _ (hG n)
      intro x hx y hy heq
      exact mul_left_cancel₀ hρ0 (hθi (hn hx.1) (hn hy.1) heq)
  have hmem : ∀ z∈ball a (ε/2) \ S, θ z∈G n ∧ θ (ρ n*z)∈G n := by
    intro z hz
    constructor
    · by_contra H
      exact hz.2 (Or.inl ⟨hz.1,H⟩)
    · by_contra H
      exact hz.2 (Or.inr ⟨hz.1,H⟩)
  have hleft : AnalyticOnNhd ℂ (fun z => H n (θ (ρ n*z)))
      (ball a (ε/2) \ S) := by
    intro z hz
    exact (hH n _ (hmem z hz).2).comp
      (f := fun z => θ (ρ n*z)) (x := z)
      ((hθ _ (Or.inr (hn hz.1))).comp (analyticAt_const.mul analyticAt_id))
  have hright : AnalyticOnNhd ℂ (fun z => H n (θ z))
      (ball a (ε/2) \ S) := by
    intro z hz
    exact (hH n _ (hmem z hz).1).comp (hθ _ (Or.inr (hB hz.1)))
  have hbS : b∈ball a (ε/2) \ S := by
    refine ⟨hbB,?_⟩
    rintro (H|H)
    · exact H.2 (hdom n hb)
    · exact H.2 (hdom n (hrotD hb))
  have heq : (fun z => H n (θ (ρ n*z))) =ᶠ[𝓝 b] (fun z => H n (θ z)) := by
    filter_upwards [isOpen_ball.mem_nhds hb] with z hz
    exact hid n z hz
  have H := hleft.eqOn_of_preconnected_of_eventuallyEq hright
    (isPathConnected_ball_sdiff_countable hS a (half_pos hε)).isConnected.isPreconnected hbS heq
  intro z hz hzg hzρ
  apply H
  refine ⟨hz,?_⟩
  rintro (h|h)
  · exact h.2 hzg
  · exact h.2 hzρ

end FunctionTheory
