module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.DiscCover
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

/-! # Complex differentiable surface charts are analytic -/
open Set Function
open scoped Manifold ContDiff
namespace AreaDeficit.Surfaces
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

theorem isManifold_analytic_of_complex : IsManifold 𝓘(ℂ) ω M := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  have hc := (IsManifold.compatible_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ)) (n := 1) he)
    (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ)) (n := 1) he')).1
  have hd : ContDiffOn ℂ 1 (e.symm ≫ₕ e') (e.symm ≫ₕ e').source := by
    simpa only [contDiffPregroupoid, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp,
      Set.preimage_id, Set.range_id, Set.inter_univ] using hc
  have ha : ContDiffOn ℂ ω (e.symm ≫ₕ e') (e.symm ≫ₕ e').source :=
    (hd.differentiableOn (by simp)).contDiffOn (e.symm ≫ₕ e').open_source
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ] using ha

end AreaDeficit.Surfaces
