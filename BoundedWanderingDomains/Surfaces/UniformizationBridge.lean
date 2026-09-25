/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DiscCover
import RiemannDynamics.Uniformization.HyperbolicSurface
import RiemannDynamics.Uniformization.PuncturedPlaneBridge

/-! # Disc-cover data from the uniformisation interface
Uses Will (Ziang) Li's path-cover and hyperbolicity formalisation, with the
projection smoothness bridge already present in this project. -/
open Set Function Metric
open scoped Manifold ContDiff
namespace AreaDeficit.Surfaces
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) ω M] [ConnectedSpace M]

/-- The intrinsic area theory applies to the existing notion of a hyperbolic surface. -/
theorem nonempty_discCover_of_isHyperbolic (h : RiemannDynamics.IsHyperbolic M) :
    Nonempty (DiscCover M) := by
  classical
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace ℂ M
  let : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  let x₀ : M := Classical.choice (inferInstance : Nonempty M)
  obtain ⟨e⟩ := h x₀
  refine ⟨{ projection := RiemannDynamics.pathCoverProj x₀ ∘ e.symm
            holomorphic := ?_
            covering := ?_
            surjective := ?_ }⟩
  · exact ((RiemannDynamics.contMDiff_pathCoverProj x₀).mdifferentiable (by simp)).comp
      (e.symm.mdifferentiable (by simp))
  · exact (RiemannDynamics.pathCoverProj_isCoveringMap x₀).comp_homeomorph e.symm.toHomeomorph
  · intro y
    let w : RiemannDynamics.PathCover x₀ :=
      ⟨y,Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ y)⟩
    refine ⟨e w,?_⟩
    change RiemannDynamics.pathCoverProj x₀ (e.symm (e w)) = y
    rw [e.symm_apply_apply]
    rfl
end AreaDeficit.Surfaces
