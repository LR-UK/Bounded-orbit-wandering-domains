/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import NoWanderingDomains.Sphere.SphereHolomorphic
import RiemannDynamics.Uniformization.SphereManifold
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! # Concrete sphere holomorphy in manifold language -/

open Set OnePoint Filter
open scoped Manifold Topology

namespace NoWanderingDomains

/-- A sphere-valued map which is holomorphic in the two standard concrete
charts is differentiable as a map to the Riemann-sphere manifold. -/
theorem SphereHolomorphicOn.mdifferentiableOn
    {f : ℂ → OnePoint ℂ} {U : Set ℂ} (hf : SphereHolomorphicOn f U) :
  MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f U := by
  intro z hz
  apply MDifferentiableAt.mdifferentiableWithinAt
  obtain ⟨V, hVo, hzV, hVU, hcase⟩ := hf z hz
  have hcont : ContinuousAt f z := hf.continuousOn.continuousAt (hf.isOpen.mem_nhds hz)
  rcases hcase with ⟨hne, hdiff⟩ | ⟨hne, hdiff⟩
  · have hsrc : f z ∈ (RiemannDynamics.sphereChartFinite).source := by
      rw [RiemannDynamics.sphereChartFinite_source]
      exact hne z hzV
    rw [mdifferentiableAt_iff_target_of_mem_source
      (f := f) (y := (((0 : ℂ) : OnePoint ℂ))) hsrc]
    refine ⟨hcont, ?_⟩
    apply DifferentiableAt.mdifferentiableAt
    have hd : DifferentiableAt ℂ (fun w => chartFiniteMap (f w)) z :=
      hdiff.differentiableAt (hVo.mem_nhds hzV)
    apply hd.congr_of_eventuallyEq
    filter_upwards [hVo.mem_nhds hzV] with w hw
    simp only [Function.comp_apply, extChartAt_coe, modelWithCornersSelf_coe,
      Function.id_comp]
    exact RiemannDynamics.sphereChartFinite_eqOn (hne w hw)
  · have hsrc : f z ∈ (RiemannDynamics.sphereChartInfty).source := by
      rw [RiemannDynamics.sphereChartInfty_source]
      exact hne z hzV
    rw [mdifferentiableAt_iff_target_of_mem_source
      (f := f) (y := (∞ : OnePoint ℂ)) hsrc]
    refine ⟨hcont, ?_⟩
    apply DifferentiableAt.mdifferentiableAt
    have hd : DifferentiableAt ℂ (fun w => chartInftyMap (f w)) z :=
      hdiff.differentiableAt (hVo.mem_nhds hzV)
    apply hd.congr_of_eventuallyEq
    filter_upwards [hVo.mem_nhds hzV] with w hw
    simp only [Function.comp_apply, extChartAt_coe, modelWithCornersSelf_coe,
      Function.id_comp]
    exact RiemannDynamics.sphereChartInfty_eqOn (hne w hw)

end NoWanderingDomains

#print axioms NoWanderingDomains.SphereHolomorphicOn.mdifferentiableOn
