import FunctionTheory.Topology.HomeomorphicDisc

open Set

namespace FunctionTheory

set_option autoImplicit false

/-- A holomorphic injection on an actual open domain supplies a conformal
chart onto its image, with both holomorphic directions recorded. -/
theorem exists_holomorphic_image_chart_of_injOn
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D) (hi : InjOn f D) :
    ∃ ψ : D ≃ₜ (f '' D),
      (∀ z : D, (ψ z : ℂ)=f z) ∧
      IsHolomorphicFunctionOn D (fun z => (ψ z : ℂ)) ∧
      IsHolomorphicFunctionOn (f '' D) (fun z => (ψ.symm z : ℂ)) := by
  have hb : BijOn f D (f '' D) := ⟨mapsTo_image f D,hi,surjOn_image f D⟩
  let ψ := hf.toHomeomorphOfBijOn hD hb
  refine ⟨ψ,fun z => rfl,isHolomorphicFunctionOn_restrict hD hf,?_⟩
  have hinv := hf.invFunOn hD hi
  have hopen : IsOpen (f '' D) := TauCeti.isOpen_image_of_differentiableOn_of_injOn hD hf hi
  have H := isHolomorphicFunctionOn_restrict hopen hinv
  simpa only [ψ,DifferentiableOn.toHomeomorphOfBijOn_symm_apply] using H

end FunctionTheory
