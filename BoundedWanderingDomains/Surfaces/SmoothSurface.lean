module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.Surfaces.ChartLaplacianSupport
public import BoundedWanderingDomains.Surfaces.SeparatingCutoff
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

/-! # Smooth localisation on an arbitrary Riemann surface

Complex differentiability of the chart transitions supplies the underlying
smooth real surface. No additional smooth structure is assumed.
-/

open Set Function Filter
open scoped Manifold Topology ContDiff

namespace AreaDeficit.Surfaces

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

/-- A one-dimensional complex manifold is a smooth real manifold with the same charts. -/
theorem isManifold_real_of_complex : IsManifold 𝓘(ℝ, ℂ) ∞ M := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  have hc := (IsManifold.compatible_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ)) (n := 1) he) (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ)) (n := 1) he')).1
  have hd : ContDiffOn ℂ 1 (e.symm ≫ₕ e') (e.symm ≫ₕ e').source := by
    simpa only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ] using hc
  have hr : ContDiffOn ℝ ∞ (e.symm ≫ₕ e') (e.symm ≫ₕ e').source :=
    ((hd.differentiableOn (by simp)).contDiffOn (e.symm ≫ₕ e').open_source).restrict_scalars ℝ
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ] using hr

/-- Compact separation supplies a smooth cutoff on every Hausdorff,
second-countable Riemann surface. Its chart Laplacian has compact support
away from both prescribed closed sets. Neither set must be compact. -/
theorem exists_surface_separating_cutoff [T2Space M] [SecondCountableTopology M]
    {K L : Set M} (hK : IsClosed K) (hL : IsClosed L) (hd : Disjoint K L)
    (hsep : SeparatedByCompact K L) :
    ∃ χ : M → ℝ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ χ ∧
      (∀ᶠ x in 𝓝ˢ K, χ x = 0) ∧ (∀ᶠ x in 𝓝ˢ L, χ x = 1) ∧
      (∀ x, χ x ∈ Icc 0 1) ∧ HasCompactSupport (chartLaplacian χ) ∧
      Disjoint (tsupport (chartLaplacian χ)) K ∧
      Disjoint (tsupport (chartLaplacian χ)) L := by
  let : IsManifold 𝓘(ℝ, ℂ) ∞ M := isManifold_real_of_complex
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ℂ M
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℂ M
  obtain ⟨D,hD,χ,hχK,hχL,hχ,hout⟩ :=
    exists_smooth_separating_cutoff 𝓘(ℝ, ℂ) hK hL hd hsep
  refine ⟨χ,χ.contMDiff,hχK,hχL,hχ,?_,
    disjoint_tsupport_chartLaplacian_of_const_near hχK,
    disjoint_tsupport_chartLaplacian_of_const_near hχL⟩
  apply hasCompactSupport_chartLaplacian hD
  intro x hx
  rcases hout x hx with h | h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩

end AreaDeficit.Surfaces
