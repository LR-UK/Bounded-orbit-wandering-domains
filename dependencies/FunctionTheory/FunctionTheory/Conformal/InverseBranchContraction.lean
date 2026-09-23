import TauCeti.Analysis.Complex.Conformal.Biholomorph
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- A holomorphic inverse branch contracts distances on a convex target
whenever the forward derivative has a positive lower bound along that branch.
Convexity is needed on the target, not on the inverse image. -/
theorem inverse_branch_dist_le_of_deriv_lower_bound
    {U V S : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hS : Convex ℝ S) (hSV : S ⊆ V)
    {f b : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hb : AnalyticOnNhd ℂ b V)
    (hbU : MapsTo b V U) (hfb : ∀ w ∈ V, f (b w) = w)
    {L : ℝ} (hL : 0 < L) (hderiv : ∀ w ∈ S, L ≤ ‖deriv f (b w)‖)
    {z w : ℂ} (hz : z ∈ S) (hw : w ∈ S) :
    dist (b z) (b w) ≤ (1 / L) * dist z w := by
  have hbD : ∀ x ∈ S, DifferentiableAt ℂ b x := fun x hx =>
    (hb x (hSV hx)).differentiableAt
  have hbnd : ∀ x ∈ S, ‖deriv b x‖ ≤ 1/L := by
    intro x hx
    have hcomp : (fun y => f (b y)) =ᶠ[𝓝 x] (fun y => y) := by
      filter_upwards [hV.mem_nhds (hSV hx)] with y hy
      exact hfb y hy
    have hdeq := hcomp.deriv_eq
    have hchain := deriv_comp x (hf (b x) (hbU (hSV hx))).differentiableAt (hbD x hx)
    have hmul : deriv f (b x) * deriv b x = 1 := by
      rw [← hchain]
      simpa [Function.comp_def] using hdeq
    have hnorm := congrArg norm hmul
    rw [norm_mul, norm_one] at hnorm
    apply (le_div_iff₀ hL).mpr
    nlinarith [hderiv x hx, norm_nonneg (deriv b x)]
  rw [dist_eq_norm, dist_eq_norm]
  exact hS.norm_image_sub_le_of_norm_deriv_le hbD hbnd hw hz

/-- In particular, inverse images of subsets of a disc have no larger
diameter when the forward derivative is at least one. -/
theorem inverse_branch_dist_le_of_one_le_deriv
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {a : ℂ} {r : ℝ} (hball : ball a r ⊆ V)
    {f b : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hb : AnalyticOnNhd ℂ b V)
    (hbU : MapsTo b V U) (hfb : ∀ w ∈ V, f (b w) = w)
    (hderiv : ∀ w ∈ ball a r, 1 ≤ ‖deriv f (b w)‖)
    {z w : ℂ} (hz : z ∈ ball a r) (hw : w ∈ ball a r) :
    dist (b z) (b w) ≤ dist z w := by
  simpa using inverse_branch_dist_le_of_deriv_lower_bound hU hV (convex_ball a r)
    hball hf hb hbU hfb (by norm_num : (0 : ℝ) < 1) hderiv hz hw

end FunctionTheory
