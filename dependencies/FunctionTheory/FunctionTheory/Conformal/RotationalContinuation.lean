import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

open Set Filter Function Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Rotations tending to the identity map the half-radius boundary collar
into the full collar, uniformly on that smaller ball. -/
theorem eventually_rotations_map_collar (ρ : ℕ → ℂ)
    (hρ : Tendsto ρ atTop (𝓝 1)) (hnorm : ∀ n, ‖ρ n‖=1)
    (a : ℂ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n in atTop, MapsTo (fun z => ρ n*z) (ball a (ε/2)) (ball a ε) := by
  have H : Tendsto (fun n => ρ n*a) atTop (𝓝 a) := by
    simpa only [one_mul] using hρ.mul_const a
  filter_upwards [H.eventually (isOpen_ball.mem_nhds (mem_ball_self (half_pos hε)))] with n hn
  intro z hz
  have heq : dist (ρ n*z) (ρ n*a)=dist z a := by
    simp only [dist_eq_norm,← mul_sub,norm_mul,hnorm n,one_mul]
  have hb : dist (ρ n*a) a<ε/2 := hn
  have hz' : dist z a<ε/2 := hz
  change dist (ρ n*z) a<ε
  calc
    dist (ρ n*z) a ≤ dist (ρ n*z) (ρ n*a)+dist (ρ n*a) a := dist_triangle _ _ _
    _ < ε := by rw [heq]; linarith

/-- A functional identity holding in the unit disc continues through a
boundary chart. The outer functions need be analytic only on the chart's
image. This lemma does not infer equality across undefined meromorphic
iterates: regularity on the displayed image is an explicit hypothesis. -/
theorem eventually_rotation_identity_across_circle
    (θ : ℂ → ℂ) (H : ℕ → ℂ → ℂ) (ρ : ℕ → ℂ)
    {a : ℂ} (ha : ‖a‖=1) {ε : ℝ} (hε : 0<ε)
    (hθ : AnalyticOnNhd ℂ θ (ball 0 1 ∪ ball a ε))
    (hH : ∀ n, AnalyticOnNhd ℂ (H n) (θ '' (ball 0 1 ∪ ball a ε)))
    (hρ : Tendsto ρ atTop (𝓝 1)) (hnorm : ∀ n, ‖ρ n‖=1)
    (hid : ∀ n, ∀ z∈ball (0:ℂ) 1, H n (θ (ρ n*z))=H n (θ z)) :
    ∀ᶠ n in atTop, ∀ z∈ball a (ε/2), H n (θ (ρ n*z))=H n (θ z) := by
  have hacl : a∈closure (ball (0:ℂ) 1) := by
    rw [closure_ball _ one_ne_zero]
    simpa only [mem_closedBall,dist_zero_right,ha] using (le_refl (1:ℝ))
  obtain ⟨b,hb,hba⟩ := Metric.mem_closure_iff.mp hacl (ε/2) (half_pos hε)
  have hbD : b∈ball a (ε/2) := by simpa only [mem_ball,dist_comm] using hba
  have hDS : ball a (ε/2) ⊆ ball (0:ℂ) 1 ∪ ball a ε :=
    fun z hz => Or.inr (ball_subset_ball (by linarith) hz)
  filter_upwards [eventually_rotations_map_collar ρ hρ hnorm a hε] with n hn
  have hleft : AnalyticOnNhd ℂ (fun z => H n (θ (ρ n*z))) (ball a (ε/2)) := by
    intro z hz
    have hmem : ρ n*z∈ball (0:ℂ) 1 ∪ ball a ε := Or.inr (hn hz)
    exact (hH n _ (mem_image_of_mem θ hmem)).comp
      (f := fun z => θ (ρ n*z)) (x := z) ((hθ _ hmem).comp (analyticAt_const.mul analyticAt_id))
  have hright : AnalyticOnNhd ℂ (fun z => H n (θ z)) (ball a (ε/2)) := by
    intro z hz
    exact (hH n _ (mem_image_of_mem θ (hDS hz))).comp (hθ _ (hDS hz))
  have hbn : ∀ᶠ z in 𝓝 b, z∈ball (0:ℂ) 1 := isOpen_ball.mem_nhds hb
  have heq : (fun z => H n (θ (ρ n*z))) =ᶠ[𝓝 b] (fun z => H n (θ z)) :=
    hbn.mono (fun z hz => hid n z hz)
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright
    (convex_ball a (ε/2)).isPreconnected hbD heq

end FunctionTheory
