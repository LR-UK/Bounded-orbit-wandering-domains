/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.MeromorphicSphereHolomorphic
import BoundedWanderingDomains.Surfaces.LocalDynamics
import BoundedWanderingDomains.Surfaces.PlaneReading

/-! # A meromorphic plane map as a local map of the sphere -/

open Set Function OnePoint Topology
open scoped Manifold Topology

namespace MeromorphicDynamics

/-- The finite part of the Riemann sphere, used as the source of a
meromorphic local map. -/
noncomputable def finiteSphereOpens : TopologicalSpace.Opens (OnePoint ℂ) :=
  ⟨RiemannDynamics.sphereChartFinite.source,
    RiemannDynamics.sphereChartFinite.open_source⟩

@[simp] theorem coe_mem_finiteSphereOpens (z : ℂ) :
    (z : OnePoint ℂ) ∈ finiteSphereOpens := by
  change (z : OnePoint ℂ) ∈ RiemannDynamics.sphereChartFinite.source
  rw [RiemannDynamics.sphereChartFinite_source]
  exact OnePoint.coe_ne_infty z

/-- A meromorphic function is a local self-map of the sphere whose source is
the finite chart. Poles are mapped to the genuine point at infinity. -/
noncomputable def surfaceModel (f : ℂ → ℂ) :
    SurfaceDynamics.LocalMap (OnePoint ℂ) where
  source := finiteSphereOpens
  map z := FunctionTheory.meromorphicSphereValue f
    (RiemannDynamics.sphereChartFinite z)

@[simp] theorem surfaceModel_source (f : ℂ → ℂ) :
    (surfaceModel f).source = finiteSphereOpens := rfl

@[simp] theorem surfaceModel_map_coe (f : ℂ → ℂ) (z : ℂ) :
    (surfaceModel f).map ⟨(z : OnePoint ℂ), coe_mem_finiteSphereOpens z⟩ =
      FunctionTheory.meromorphicSphereValue f z := by
  simp [surfaceModel]

/-- The sphere model is intrinsically holomorphic on its actual source. -/
theorem surfaceModel_mdifferentiable {f : ℂ → ℂ}
    (hf : MeromorphicNFOn f Set.univ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (surfaceModel f).map := by
  have hsphere :=
    FunctionTheory.MeromorphicNFOn.mdifferentiable_meromorphicSphereValue hf
  have hchart : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun z : finiteSphereOpens => RiemannDynamics.sphereChartFinite (z : OnePoint ℂ)) := by
    intro z
    exact (mdifferentiableAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas ((0 : ℂ) : OnePoint ℂ)) z.2).comp z
        (AreaDeficit.Surfaces.mdifferentiable_subtype_val finiteSphereOpens z)
  exact hsphere.comp hchart

theorem continuous_surfaceModel_map {f : ℂ → ℂ}
    (hf : MeromorphicNFOn f Set.univ) : Continuous (surfaceModel f).map :=
  (surfaceModel_mdifferentiable hf).continuous

@[simp] theorem surfaceModel_step_coe (f : ℂ → ℂ) (z : ℂ) :
    (surfaceModel f).step (z : OnePoint ℂ) =
      Option.some (FunctionTheory.meromorphicSphereValue f z) := by
  simp [SurfaceDynamics.LocalMap.step, surfaceModel]

/-- On an orbit segment containing no pole, partial sphere iteration agrees
with ordinary iteration of the chosen finite representative. -/
theorem surfaceModel_iterate_coe_of_analytic
    (f : ℂ → ℂ) (n : ℕ) (z : ℂ)
    (h : ∀ j < n, AnalyticAt ℂ f ((f^[j]) z)) :
    (surfaceModel f).iterate n (z : OnePoint ℂ) =
      Option.some (((f^[n]) z : ℂ) : OnePoint ℂ) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      rw [SurfaceDynamics.LocalMap.iterate_succ _ n _ (coe_mem_finiteSphereOpens z)]
      rw [surfaceModel_map_coe]
      have ha0 : AnalyticAt ℂ f z := by
        simpa using h 0 (Nat.zero_lt_succ n)
      rw [FunctionTheory.meromorphicSphereValue_of_analytic ha0]
      rw [Function.iterate_succ_apply]
      apply ih
      intro j hj
      simpa only [Function.iterate_succ_apply] using
        h (j + 1) (Nat.succ_lt_succ hj)

end MeromorphicDynamics

#print axioms MeromorphicDynamics.surfaceModel_mdifferentiable
#print axioms MeromorphicDynamics.surfaceModel_iterate_coe_of_analytic
