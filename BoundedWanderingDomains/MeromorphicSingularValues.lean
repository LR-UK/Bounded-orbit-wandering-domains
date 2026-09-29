module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.MeromorphicSurfaceModel
public import BoundedWanderingDomains.SingularValues
public import FunctionTheory.Conformal.LittlePicardBloch

@[expose] public section

/-! # Singular values of the sphere model

The sphere-valued definition treats poles as ordinary points of the source
and includes omitted values among singular values. It agrees exactly with
the intrinsic local-map definition under the finite source chart.
-/

open Set Function OnePoint
open scoped Topology Manifold

namespace MeromorphicDynamics

/-- Values with a neighbourhood covered surjectively by the honest
sphere-valued meromorphic map. -/
def regularValues (f : ℂ → ℂ) : Set (OnePoint ℂ) :=
  {y | ∃ W : Set (OnePoint ℂ), IsOpen W ∧ y ∈ W ∧
    W ⊆ range (FunctionTheory.meromorphicSphereValue f) ∧
    IsCoveringMapOn (FunctionTheory.meromorphicSphereValue f) W}

/-- Singular values on the sphere, including any omitted values. -/
def singularValues (f : ℂ → ℂ) : Set (OnePoint ℂ) := (regularValues f)ᶜ

theorem surfaceModel_singularValues (f : ℂ → ℂ) :
    (surfaceModel f).singularValues = singularValues f := by
  have hrange : range (surfaceModel f).map =
      range (FunctionTheory.meromorphicSphereValue f) := by
    change range (FunctionTheory.meromorphicSphereValue f ∘ finiteSphereHomeomorph.symm) = _
    rw [range_comp, finiteSphereHomeomorph.symm.surjective.range_eq, image_univ]
  ext y
  simp only [SurfaceDynamics.LocalMap.singularValues, singularValues, mem_compl_iff]
  apply not_congr
  change (∃ W, IsOpen W ∧ y ∈ W ∧ W ⊆ range (surfaceModel f).map ∧
      IsCoveringMapOn (surfaceModel f).map W) ↔ _
  rw [hrange]
  change (∃ W, IsOpen W ∧ y ∈ W ∧ W ⊆ range (FunctionTheory.meromorphicSphereValue f) ∧
      IsCoveringMapOn (FunctionTheory.meromorphicSphereValue f ∘ finiteSphereHomeomorph.symm) W) ↔ _
  simp only [IsCoveringMapOn.comp_homeomorph_iff, regularValues, mem_ofPred_eq]

/-- An entire map has the expected finite-chart realization. -/
theorem meromorphicSphereValue_eq_coe_of_entire {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) :
    FunctionTheory.meromorphicSphereValue f = fun z => (f z : OnePoint ℂ) := by
  funext z
  exact FunctionTheory.meromorphicSphereValue_of_analytic (hf.analyticAt z)

/-- A finite plane singular set gives a finite sphere singular set.
The auxiliary omitted-value set is at most a singleton by Little Picard;
this also reconciles the plane covering convention, which permits empty fibres.
-/
theorem finite_singularValues_of_entire {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hnonconst : ¬ ∃ c, ∀ z, f z = c)
    (hfinite : (ComplexDynamics.singularValues f).Finite) :
    (singularValues f).Finite := by
  have hopen : IsOpenMap f :=
    (show AnalyticOnNhd ℂ f univ from fun z _ => hf.analyticAt z).is_constant_or_isOpenMap.resolve_left
      hnonconst
  have homit : (range f)ᶜ.Subsingleton := by
    intro a ha b hb
    by_contra hab
    obtain ⟨c, hc⟩ := FunctionTheory.exists_eq_const_of_two_omitted_values hf hab
      (fun z h => ha ⟨z, h⟩) (fun z h => hb ⟨z, h⟩)
    exact hnonconst ⟨c, fun z => congrFun hc z⟩
  apply ((hfinite.union homit.finite).image ((↑) : ℂ → OnePoint ℂ)).insert ∞ |>.subset
  intro y hy
  cases y with
  | infty => exact mem_insert _ _
  | coe w =>
    by_contra hw
    have hw' : w ∉ ComplexDynamics.singularValues f ∪ (range f)ᶜ := by
      intro h
      exact hw (mem_insert_of_mem _ ⟨w, h, rfl⟩)
    have hwreg : w ∈ ComplexDynamics.regularValueSet f := by
      by_contra h
      exact hw' (Or.inl h)
    have hwrange : w ∈ range f := by
      by_contra h
      exact hw' (Or.inr h)
    obtain ⟨V, hVo, hwV, hcov⟩ := hwreg
    let W := V ∩ range f
    have hWo : IsOpen W := hVo.inter (hopen.isOpen_range)
    apply hy
    refine ⟨((↑) : ℂ → OnePoint ℂ) '' W,
      OnePoint.isOpenEmbedding_coe.isOpenMap W hWo, ⟨w, ⟨hwV, hwrange⟩, rfl⟩, ?_, ?_⟩
    · rintro _ ⟨v, ⟨_, z, rfl⟩, rfl⟩
      refine ⟨z, ?_⟩
      rw [meromorphicSphereValue_eq_coe_of_entire hf]
    · rintro _ ⟨v, hv, rfl⟩
      have h := (hcov v hv.1).homeomorph_comp finiteSphereHomeomorph
      have h' := @IsEvenlyCovered.subtypeVal_comp ℂ (OnePoint ℂ) _ _
        (finiteSphereOpens : Set (OnePoint ℂ)) (f ⁻¹' {v}) _
        finiteSphereOpens.isOpen (finiteSphereHomeomorph v)
        (finiteSphereHomeomorph ∘ f) h
      rw [meromorphicSphereValue_eq_coe_of_entire hf]
      exact h'.to_isEvenlyCovered_preimage

end MeromorphicDynamics
