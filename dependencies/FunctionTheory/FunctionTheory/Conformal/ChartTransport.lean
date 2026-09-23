import FunctionTheory.Holomorphic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Topology.Homeomorph.Lemmas

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

theorem IsHolomorphicFunctionOn.comp {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) {f : U → V} {g : V → ℂ}
    (hg : IsHolomorphicFunctionOn V g)
    (hf : IsHolomorphicFunctionOn U (fun z => (f z : ℂ))) :
    IsHolomorphicFunctionOn U (fun z => g (f z)) := by
  let F : ℂ → ℂ := domainExtension (fun z => (f z : ℂ))
  have hF : MapsTo F U V := by
    intro z hz
    simpa only [F, domainExtension_apply _ z hz] using (f ⟨z, hz⟩).property
  have hcomp := (hg.differentiableOn_extension hV).comp
    (hf.differentiableOn_extension hU) hF
  have h := isHolomorphicFunctionOn_restrict hU hcomp
  convert h using 1
  ext z
  simp [domainExtension_apply]

section Charts

variable {D V W : Type*} [TopologicalSpace D] [TopologicalSpace V] [TopologicalSpace W]

/-- Transport a chart backwards through an isomorphism of its target. -/
def pullbackChart (q : V ≃ₜ W) (ψ : D ≃ₜ W) : D ≃ₜ V := ψ.trans q.symm

@[simp] theorem pullbackChart_step (q : V ≃ₜ W) (ψ : D ≃ₜ W) (z : D) :
    q (pullbackChart q ψ z) = ψ z := by
  simp [pullbackChart]

/-- The associated map between the transported charts is exactly the identity. -/
theorem pullbackChart_associated_eq_id (q : V ≃ₜ W) (ψ : D ≃ₜ W) :
    (fun z => ψ.symm (q (pullbackChart q ψ z))) = id := by
  funext z
  simp

/-- A return conjugacy becomes a one-step conjugacy after transporting the next chart. -/
theorem pullbackChart_prescribed_step {S : Type*} [TopologicalSpace S]
    (q : V ≃ₜ W) (ψ : D ≃ₜ W) (α : D ≃ₜ S)
    (F : S → V) (b : D → D)
    (h : ∀ z, q (F (α z)) = ψ (b z)) :
    (fun z => (pullbackChart q ψ).symm (F (α z))) = b := by
  funext z
  simp only [pullbackChart, Homeomorph.symm_trans_apply,
    Homeomorph.symm_symm]
  rw [h z, Homeomorph.symm_apply_apply]

/-- Compatible tail maps to a common endpoint give identity associated functions. -/
theorem pullbackChart_tail_step {V' : Type*} [TopologicalSpace V']
    (q : V ≃ₜ W) (r : V' ≃ₜ W) (ψ : D ≃ₜ W) (F : V → V')
    (h : ∀ z, r (F z) = q z) :
    (fun z => (pullbackChart r ψ).symm (F (pullbackChart q ψ z))) = id := by
  funext z
  simp only [pullbackChart, Homeomorph.symm_trans_apply, Homeomorph.symm_symm,
    Homeomorph.trans_apply, h, Homeomorph.apply_symm_apply, Homeomorph.symm_apply_apply,
    id_eq]

end Charts

/-- Pulling a holomorphic chart back through a conformal isomorphism preserves both
holomorphic directions. All functions are defined on their actual domains. -/
theorem pullbackChart_holomorphic {D V W : Set ℂ}
    (hD : IsOpen D) (hV : IsOpen V) (hW : IsOpen W)
    (q : V ≃ₜ W) (ψ : D ≃ₜ W)
    (hq : IsHolomorphicFunctionOn V (fun z => (q z : ℂ)))
    (hqi : IsHolomorphicFunctionOn W (fun z => (q.symm z : ℂ)))
    (hψ : IsHolomorphicFunctionOn D (fun z => (ψ z : ℂ)))
    (hψi : IsHolomorphicFunctionOn W (fun z => (ψ.symm z : ℂ))) :
    IsHolomorphicFunctionOn D (fun z => (pullbackChart q ψ z : ℂ)) ∧
      IsHolomorphicFunctionOn V (fun z => ((pullbackChart q ψ).symm z : ℂ)) := by
  exact ⟨hqi.comp hD hW hψ, hψi.comp hV hW hq⟩

end FunctionTheory
