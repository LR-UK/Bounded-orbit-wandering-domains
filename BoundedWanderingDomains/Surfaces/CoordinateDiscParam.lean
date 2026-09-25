/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CoordinateDiskSelection
import BoundedWanderingDomains.Surfaces.DiscDilation
import BoundedWanderingDomains.Surfaces.HolomorphicLifting

/-! # Holomorphic parametrisation of a surface coordinate disc -/

open Set Function Metric
open AreaDeficit.Surfaces
open scoped Manifold Topology

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X]

namespace RiemannDynamics.CoordDisk

noncomputable def param (D : RiemannDynamics.CoordDisk X) (z : unitDisc) : X :=
  (chartAt ℂ D.center).symm
    ((chartAt ℂ D.center D.center) + ((D.radius / 2 : ℝ) : ℂ) * (z : ℂ))

theorem param_argument_mem_target (D : RiemannDynamics.CoordDisk X)
    (z : unitDisc) :
    (chartAt ℂ D.center D.center) + ((D.radius / 2 : ℝ) : ℂ) * (z : ℂ) ∈
      (chartAt ℂ D.center).target := by
  apply D.closedBall_subset
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (le_of_lt (half_pos D.radius_pos))]
  have hz : ‖(z : ℂ)‖ < 1 := mem_ball_zero_iff.mp z.property
  nlinarith [D.radius_pos]

theorem mdifferentiable_param (D : RiemannDynamics.CoordDisk X) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) D.param := by
  intro z
  let a : unitDisc → ℂ := fun u =>
    (chartAt ℂ D.center D.center) + ((D.radius / 2 : ℝ) : ℂ) * (u : ℂ)
  have ha : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) a z := by
    change MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun u : unitDisc =>
      (chartAt ℂ D.center D.center) + ((D.radius / 2 : ℝ) : ℂ) * (u : ℂ)) z
    exact (mdifferentiableAt_subtype_iff
      (U := unitDisc)
      (f := fun u : ℂ => (chartAt ℂ D.center D.center) +
        ((D.radius / 2 : ℝ) : ℂ) * u) (x := z)).mpr
      (((differentiableAt_const
        (chartAt ℂ D.center D.center)).add
        ((differentiableAt_const ((D.radius / 2 : ℝ) : ℂ)).mul
          differentiableAt_id)).mdifferentiableAt)
  have hs : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (chartAt ℂ D.center).symm (a z) :=
    mdifferentiableAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas _) (D.param_argument_mem_target z)
  exact hs.comp z ha

@[simp] theorem param_zero (D : RiemannDynamics.CoordDisk X) :
    D.param discZero = D.center := by
  unfold param
  change (chartAt ℂ D.center).symm
    ((chartAt ℂ D.center D.center) + ((D.radius / 2 : ℝ) : ℂ) * 0) = D.center
  rw [mul_zero, add_zero]
  exact (chartAt ℂ D.center).left_inv (mem_chart_source ℂ D.center)

theorem param_mem_closedCarrier (D : RiemannDynamics.CoordDisk X)
    (z : unitDisc) : D.param z ∈ D.closedCarrier := by
  refine ⟨(chartAt ℂ D.center D.center) +
      ((D.radius / 2 : ℝ) : ℂ) * (z : ℂ), ?_, rfl⟩
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (le_of_lt (half_pos D.radius_pos))]
  have hz : ‖(z : ℂ)‖ < 1 := mem_ball_zero_iff.mp z.property
  nlinarith [D.radius_pos]

theorem injective_param (D : RiemannDynamics.CoordDisk X) :
    Function.Injective D.param := by
  intro z w hzw
  have hz := (chartAt ℂ D.center).right_inv (D.param_argument_mem_target z)
  have hw := (chartAt ℂ D.center).right_inv (D.param_argument_mem_target w)
  have he := congrArg (chartAt ℂ D.center) hzw
  unfold param at he
  rw [hz, hw] at he
  have hr : ((D.radius / 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (half_pos D.radius_pos))
  apply Subtype.ext
  exact mul_left_cancel₀ hr (add_left_cancel he)

end RiemannDynamics.CoordDisk

#print axioms RiemannDynamics.CoordDisk.mdifferentiable_param
