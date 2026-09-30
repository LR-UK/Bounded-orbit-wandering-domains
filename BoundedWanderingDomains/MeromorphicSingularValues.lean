module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.MeromorphicSurfaceModel
public import BoundedWanderingDomains.SphericalSingularValues

@[expose] public section

/-! # Singular values of the sphere model

The sphere-valued definition treats poles as ordinary points of the source
and permits empty covering neighbourhoods. It agrees exactly with
the intrinsic local-map definition under the finite source chart.
-/

open Set Function OnePoint
open scoped Topology Manifold

namespace MeromorphicDynamics

/-- Values with a covering neighbourhood for the sphere-valued map;
empty sheets are allowed. -/
def regularValues (f : ℂ → ℂ) : Set (OnePoint ℂ) :=
  SurfaceDynamics.Map.regularValues (FunctionTheory.meromorphicSphereValue f)

/-- Singular values of the genuine sphere-valued map. -/
def singularValues (f : ℂ → ℂ) : Set (OnePoint ℂ) := (regularValues f)ᶜ

theorem surfaceModel_singularValues (f : ℂ → ℂ) :
    (surfaceModel f).singularValues = singularValues f := by
  ext y
  simp only [SurfaceDynamics.LocalMap.singularValues, singularValues, mem_compl_iff]
  apply not_congr
  change (∃ W, IsOpen W ∧ y ∈ W ∧
      IsCoveringMapOn (FunctionTheory.meromorphicSphereValue f ∘ finiteSphereHomeomorph.symm) W) ↔ _
  simp only [IsCoveringMapOn.comp_homeomorph_iff, regularValues,
    SurfaceDynamics.Map.regularValues, mem_ofPred_eq]

/-- An entire map has the expected finite-chart realization. -/
theorem meromorphicSphereValue_eq_coe_of_entire {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) :
    FunctionTheory.meromorphicSphereValue f = fun z => (f z : OnePoint ℂ) := by
  funext z
  exact FunctionTheory.meromorphicSphereValue_of_analytic (hf.analyticAt z)

/-- The sphere singular set is contained in the spherical entire singular set. -/
theorem singularValues_subset_of_entire {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) :
    singularValues f ⊆ ComplexDynamics.sphericalSingularValues f := by
  intro y hy
  cases y with
  | infty => exact mem_insert _ _
  | coe w =>
    by_contra hw
    have hwreg : w ∈ ComplexDynamics.regularValueSet f := by
      by_contra h
      exact hw (mem_insert_of_mem _ ⟨w, h, rfl⟩)
    obtain ⟨V, hVo, hwV, hcov⟩ := hwreg
    apply hy
    refine ⟨((↑) : ℂ → OnePoint ℂ) '' V,
      OnePoint.isOpenEmbedding_coe.isOpenMap V hVo, ⟨w, hwV, rfl⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    have h := (hcov v hv).homeomorph_comp finiteSphereHomeomorph
    have h' := @IsEvenlyCovered.subtypeVal_comp ℂ (OnePoint ℂ) _ _
      (finiteSphereOpens : Set (OnePoint ℂ)) (f ⁻¹' {v}) _
      finiteSphereOpens.isOpen (finiteSphereHomeomorph v)
      (finiteSphereHomeomorph ∘ f) h
    rw [meromorphicSphereValue_eq_coe_of_entire hf]
    exact h'.to_isEvenlyCovered_preimage

/-- Entire finite singular sets remain finite in the sphere convention. -/
theorem finite_singularValues_of_entire {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfinite : (ComplexDynamics.singularValues f).Finite) :
    (singularValues f).Finite :=
  ((hfinite.image ((↑) : ℂ → OnePoint ℂ)).insert ∞).subset (singularValues_subset_of_entire hf)

/-- The entire derived-set conclusion follows by monotonicity. -/
theorem derived_singularValues_subset_of_entire {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) :
    derivedSet (singularValues f) ⊆ derivedSet (ComplexDynamics.sphericalSingularValues f) :=
  derivedSet_mono _ _ (singularValues_subset_of_entire hf)

end MeromorphicDynamics
