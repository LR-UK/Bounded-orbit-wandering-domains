import FunctionTheory.Holomorphic
import Mathlib.Analysis.Complex.OpenMapping

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Openness of a holomorphic map on its actual domain is equivalent to
local nonconstancy everywhere. The domain need not be connected. -/
theorem isOpenMap_restrict_iff_locally_nonconstant
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) :
    IsOpenMap (fun z : U => f z) ↔
      ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, f z = f a := by
  constructor
  · intro hopen a ha hconst
    obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_ball.eventually_iff.mp
      ((hU.eventually_mem ha).and hconst)
    have hs : IsOpen ((fun z : U => f z) ''
        ((Subtype.val : U → ℂ) ⁻¹' ball a r)) :=
      hopen _ (isOpen_ball.preimage continuous_subtype_val)
    have heq : ((fun z : U => f z) '' ((Subtype.val : U → ℂ) ⁻¹' ball a r)) =
        {f a} := by
      ext v
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (hball hz).2
      · intro hv
        rcases mem_singleton_iff.mp hv with rfl
        exact ⟨⟨a, ha⟩, mem_ball_self hr, rfl⟩
    exact not_isOpen_singleton (f a) (heq ▸ hs)
  · intro hnc s hs
    have ht : IsOpen (Subtype.val '' s) := hU.isOpenMap_subtype_val s hs
    have himage : IsOpen (f '' (Subtype.val '' s)) := by
      apply isOpen_iff_mem_nhds.mpr
      rintro v ⟨a, ha, rfl⟩
      have haU : a ∈ U := by obtain ⟨a, _, rfl⟩ := ha; exact a.property
      exact ((hf a haU).eventually_constant_or_nhds_le_map_nhds.resolve_left
        (hnc a haU)) (image_mem_map (ht.mem_nhds ha))
    simpa only [image_image, Function.comp_def] using himage

/-- Actual-domain formulation of the open mapping equivalence. -/
theorem IsHolomorphicFunctionOn.isOpenMap_iff_locally_nonconstant
    {U : Set ℂ} (hU : IsOpen U) {f : U → ℂ} (hf : IsHolomorphicFunctionOn U f) :
    IsOpenMap f ↔ ∀ a : U, ¬ ∀ᶠ z in 𝓝 (a : ℂ),
      domainExtension f z = f a := by
  have heq : (fun z : U => domainExtension f z) = f := by
    funext z
    exact domainExtension_apply f z z.property
  have h := isOpenMap_restrict_iff_locally_nonconstant hU
    ((hf.differentiableOn_extension hU).analyticOnNhd hU)
  rw [heq] at h
  constructor
  · intro hopen a
    simpa only [domainExtension_apply f a a.property] using h.mp hopen a a.property
  · intro hnc
    apply h.mpr
    intro a ha
    simpa only [domainExtension_apply f a ha] using hnc ⟨a, ha⟩

end FunctionTheory
