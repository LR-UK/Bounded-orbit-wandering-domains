module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.CoordinateDiskSelection
public import BoundedWanderingDomains.Surfaces.DiscDilation
public import BoundedWanderingDomains.Surfaces.HolomorphicLifting

@[expose] public section

/-! # Holomorphic parametrisation of a surface coordinate disc -/

open Set Function Metric
open Topology
open AreaDeficit.Surfaces
open scoped Manifold Topology

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X]

namespace RiemannDynamics.CoordDisk

noncomputable def param (D : RiemannDynamics.CoordDisk X) (z : unitDisc) : X :=
  (chartAt ℂ D.center).symm
    ((chartAt ℂ D.center D.center) + ((D.radius / 2 : ℝ) : ℂ) * (z : ℂ))

omit [IsManifold 𝓘(ℂ, ℂ) 1 X] in
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

omit [IsManifold 𝓘(ℂ, ℂ) 1 X] in
@[simp] theorem param_zero (D : RiemannDynamics.CoordDisk X) :
    D.param discZero = D.center := by
  unfold param
  change (chartAt ℂ D.center).symm
    ((chartAt ℂ D.center D.center) + ((D.radius / 2 : ℝ) : ℂ) * 0) = D.center
  rw [mul_zero, add_zero]
  exact (chartAt ℂ D.center).left_inv (mem_chart_source ℂ D.center)

omit [IsManifold 𝓘(ℂ, ℂ) 1 X] in
theorem param_mem_closedCarrier (D : RiemannDynamics.CoordDisk X)
    (z : unitDisc) : D.param z ∈ D.closedCarrier := by
  refine ⟨(chartAt ℂ D.center D.center) +
      ((D.radius / 2 : ℝ) : ℂ) * (z : ℂ), ?_, rfl⟩
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (le_of_lt (half_pos D.radius_pos))]
  have hz : ‖(z : ℂ)‖ < 1 := mem_ball_zero_iff.mp z.property
  nlinarith [D.radius_pos]

omit [IsManifold 𝓘(ℂ) 1 X] in
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

/-- A centred coordinate-disc parametrisation identifies the unit disc
with an open surface neighbourhood of its centre. -/
theorem isOpenEmbedding_param (D : RiemannDynamics.CoordDisk X) :
    IsOpenEmbedding D.param := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact D.mdifferentiable_param.continuous
  · exact D.injective_param
  · intro s hs
    let a : ℂ := ((D.radius / 2 : ℝ) : ℂ)
    let b : ℂ := chartAt ℂ D.center D.center
    have ha : a ≠ 0 := by
      dsimp [a]
      exact_mod_cast (ne_of_gt (half_pos D.radius_pos))
    let e : ℂ ≃ₜ ℂ := affineHomeomorph a b ha
    let T : Set ℂ := e '' ((Subtype.val : unitDisc → ℂ) '' s)
    have hval : IsOpen ((Subtype.val : unitDisc → ℂ) '' s) :=
      (show IsOpenEmbedding (Subtype.val : unitDisc → ℂ) from
        unitDisc.isOpen.isOpenEmbedding_subtypeVal).isOpenMap s hs
    have hTopen : IsOpen T := e.isOpenMap _ hval
    have hTtarget : T ⊆ (chartAt ℂ D.center).target := by
      rintro y ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [e, a, b, affineHomeomorph_apply, mul_comm, add_comm] using
        D.param_argument_mem_target z
    have hopen := (chartAt ℂ D.center).isOpen_image_symm_of_subset_target
      hTopen hTtarget
    convert hopen using 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨e (z : ℂ), ⟨(z : ℂ), ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
      simp only [param, e, a, b, affineHomeomorph_apply, mul_comm, add_comm]
    · rintro ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
      refine ⟨z, hz, ?_⟩
      simp only [param, e, a, b, affineHomeomorph_apply, mul_comm, add_comm]

end RiemannDynamics.CoordDisk
