import EremenkosConjecture.Univalence
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Uniform local estimates without compactness

Uniform disk margins give derivative control and coverage for a holomorphic
perturbation of the identity. Together with `injOn_of_close_to_id` these are
the ingredients needed on the unbounded strips of Section 4.
-/

open Set Metric Function Filter
open scoped Topology

namespace EremenkosConjecture

theorem norm_deriv_sub_le_of_close_on_ball {f g : ℂ → ℂ} {z : ℂ} {r δ : ℝ}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball z r))
    (hg : DifferentiableOn ℂ g (ball z r))
    (hclose : ∀ w ∈ ball z r, ‖f w - g w‖ ≤ δ) :
    ‖deriv f z - deriv g z‖ ≤ 2 * δ / r := by
  let d : ℂ → ℂ := fun w => f w - g w
  have hd : DifferentiableOn ℂ d (ball z r) := hf.sub hg
  have hmaps : MapsTo d (ball z r) (closedBall (d z) (2 * δ)) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm]
    calc
      ‖d w - d z‖ ≤ ‖d w‖ + ‖d z‖ := norm_sub_le _ _
      _ ≤ δ + δ := add_le_add (hclose w hw) (hclose z (mem_ball_self hr))
      _ = 2 * δ := by ring
  have H := Complex.norm_deriv_le_div_of_mapsTo_ball hd hmaps hr
  have hderiv : deriv d z = deriv f z - deriv g z :=
    ((hf.differentiableAt (ball_mem_nhds z hr)).hasDerivAt.sub
      (hg.differentiableAt (ball_mem_nhds z hr)).hasDerivAt).deriv
  rwa [hderiv] at H

/-- A sufficiently small holomorphic perturbation of the identity covers
the centre of a disk. The preimage stays in that closed disk. -/
theorem exists_preimage_of_close_to_id_on_closedBall {U : Set ℂ}
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    {z : ℂ} {r δ : ℝ} (hr : 0 < r) (hδ : δ < r / 4)
    (hball : closedBall z r ⊆ U)
    (hclose : ∀ w ∈ U, ‖f w - w‖ ≤ δ) :
    ∃ w ∈ closedBall z r, f w = z := by
  have hzU : z ∈ U := hball (mem_closedBall_self hr.le)
  have hfb : DifferentiableOn ℂ f (ball z r) := hf.mono (ball_subset_closedBall.trans hball)
  have hdf := norm_deriv_sub_le_of_close_on_ball hr hfb differentiableOn_id
    (fun w hw => hclose w (hball (ball_subset_closedBall hw)))
  simp only [deriv_id] at hdf
  have hratio : 2 * δ / r < 1 := by rw [div_lt_one hr]; linarith
  have hdf0 : deriv f z ≠ 0 := by
    intro hzero
    simp only [hzero, zero_sub, norm_neg, norm_one] at hdf
    linarith
  have hnonconstant : ∃ᶠ w in 𝓝 z, f w ≠ f z := by
    by_contra hn
    have he : f =ᶠ[𝓝 z] (fun _ => f z) := by
      filter_upwards [not_frequently.mp hn] with w hw
      exact not_not.mp hw
    exact hdf0 (by simpa only [deriv_const] using he.deriv_eq)
  have hcont : DiffContOnCl ℂ f (ball z r) := by
    refine ⟨hfb, ?_⟩
    rw [closure_ball z hr.ne']
    exact hf.continuousOn.mono hball
  have hboundary : ∀ w ∈ sphere z r, r - 2 * δ ≤ ‖f w - f z‖ := by
    intro w hw
    have hwU := hball (sphere_subset_closedBall hw)
    have hc1 : dist w (f w) ≤ δ := by simpa only [dist_eq_norm, norm_sub_rev] using hclose w hwU
    have hc2 : dist (f z) z ≤ δ := by simpa only [dist_eq_norm] using hclose z hzU
    have hd1 := dist_triangle w (f w) z
    have hd2 := dist_triangle (f w) (f z) z
    have hwr : dist w z = r := mem_sphere.mp hw
    rw [hwr] at hd1
    rw [dist_eq_norm (f w) (f z)] at hd2
    linarith
  apply hcont.ball_subset_image_closedBall hr hboundary hnonconstant
  rw [mem_ball]
  have hcz : dist z (f z) ≤ δ := by simpa only [dist_eq_norm, norm_sub_rev] using hclose z hzU
  linarith

end EremenkosConjecture
