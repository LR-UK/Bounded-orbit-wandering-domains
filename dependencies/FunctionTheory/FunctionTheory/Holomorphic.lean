import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # Holomorphic functions on their actual domains

The input is a function on the subtype `U`. Local representatives connect it
to Mathlib's differential calculus without prescribing values outside `U`.
-/

open Filter Set
open scoped Topology

namespace FunctionTheory

/-- Holomorphy of a function on its actual domain, expressed using local
complex-differentiable representatives. For an open `U` this is the usual notion. -/
def IsHolomorphicFunctionOn (U : Set ℂ) (f : U → ℂ) : Prop :=
  ∀ z : U, ∃ g : ℂ → ℂ, DifferentiableAt ℂ g z ∧
    ∀ᶠ w in 𝓝 (z : ℂ), ∀ hw : w ∈ U, f ⟨w, hw⟩ = g w

/-- An internal extension used to apply ambient-domain calculus. -/
noncomputable def domainExtension {U : Set ℂ} (f : U → ℂ) (z : ℂ) : ℂ :=
  by
    classical
    exact if hz : z ∈ U then f ⟨z, hz⟩ else 0

@[simp] theorem domainExtension_apply {U : Set ℂ} (f : U → ℂ)
    (z : ℂ) (hz : z ∈ U) : domainExtension f z = f ⟨z, hz⟩ := by
  simp [domainExtension, hz]

theorem IsHolomorphicFunctionOn.differentiableOn_extension
    {U : Set ℂ} (hU : IsOpen U) {f : U → ℂ}
    (hf : IsHolomorphicFunctionOn U f) : DifferentiableOn ℂ (domainExtension f) U := by
  intro z hz
  obtain ⟨g, hg, heq⟩ := hf ⟨z, hz⟩
  have heq' : domainExtension f =ᶠ[𝓝 z] g := by
    filter_upwards [hU.mem_nhds hz, heq] with w hw hgw
    exact (domainExtension_apply f w hw).trans (hgw hw)
  exact (hg.congr_of_eventuallyEq heq').differentiableWithinAt

theorem isHolomorphicFunctionOn_restrict {U : Set ℂ} (hU : IsOpen U)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) :
    IsHolomorphicFunctionOn U (fun z => g z) := by
  intro z
  exact ⟨g, hg.differentiableAt (hU.mem_nhds z.property), Filter.Eventually.of_forall
    (fun _ _ => rfl)⟩

end FunctionTheory
