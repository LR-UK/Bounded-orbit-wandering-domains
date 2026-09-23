import FunctionTheory.Holomorphic
import Mathlib.Analysis.Meromorphic.Basic

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Meromorphy for a function supplied only on its actual domain. Values at poles
are irrelevant to meromorphy, as in Mathlib's `MeromorphicAt`. -/
def IsMeromorphicFunctionOn (U : Set ℂ) (f : U → ℂ) : Prop :=
  ∀ z : U, ∃ g : ℂ → ℂ, MeromorphicAt g z ∧
    ∀ᶠ w in 𝓝 (z : ℂ), ∀ hw : w ∈ U, f ⟨w, hw⟩ = g w

/-- The internal extension is meromorphic on the open domain. -/
theorem IsMeromorphicFunctionOn.meromorphicOn_extension
    {U : Set ℂ} (hU : IsOpen U) {f : U → ℂ}
    (hf : IsMeromorphicFunctionOn U f) : MeromorphicOn (domainExtension f) U := by
  intro z hz
  obtain ⟨g, hg, heq⟩ := hf ⟨z, hz⟩
  apply hg.congr
  apply Filter.EventuallyEq.filter_mono _ nhdsWithin_le_nhds
  filter_upwards [hU.mem_nhds hz, heq] with w hw hgw
  exact (hgw hw).symm.trans (domainExtension_apply f w hw).symm

/-- Restriction of an ambient meromorphic function to its open domain. -/
theorem isMeromorphicFunctionOn_restrict {U : Set ℂ}
    {g : ℂ → ℂ} (hg : MeromorphicOn g U) :
    IsMeromorphicFunctionOn U (fun z => g z) := by
  intro z
  exact ⟨g, hg z z.property, Filter.Eventually.of_forall (fun _ _ => rfl)⟩

/-- Meromorphy on an open actual domain agrees with Mathlib meromorphy of the extension. -/
theorem isMeromorphicFunctionOn_iff_extension {U : Set ℂ} (hU : IsOpen U)
    {f : U → ℂ} :
    IsMeromorphicFunctionOn U f ↔ MeromorphicOn (domainExtension f) U := by
  constructor
  · exact fun h => h.meromorphicOn_extension hU
  · intro h
    convert isMeromorphicFunctionOn_restrict h using 1
    ext z
    exact (domainExtension_apply f z z.property).symm

end FunctionTheory
