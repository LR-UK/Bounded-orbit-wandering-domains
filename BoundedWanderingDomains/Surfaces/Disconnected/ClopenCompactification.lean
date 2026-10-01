module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import Mathlib.Topology.Compactification.OnePoint.Basic

@[expose] public section

/-! # Compactifications of a union of ambient components -/

open Set Filter Topology TopologicalSpace OnePoint

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem continuous_onePoint_clopen_inclusion (O : Opens X) (hO : IsClosed (O : Set X)) :
    Continuous (OnePoint.map (Subtype.val : O → X)) := by
  apply OnePoint.continuous_map continuous_subtype_val
  rw [coclosedCompact_eq_cocompact, coclosedCompact_eq_cocompact]
  exact hO.isClosedEmbedding_subtypeVal.tendsto_cocompact

noncomputable def clopenCollapseValue (O : Opens X) (x : X) : OnePoint O := by
  classical
  exact if hx : x ∈ O then (⟨x, hx⟩ : O) else ∞

omit [T2Space X] in
theorem continuous_clopenCollapseValue (O : Opens X) (hO : IsClosed (O : Set X)) :
    Continuous (clopenCollapseValue O) := by
  classical
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ O
  · have hi : IsOpenEmbedding (Subtype.val : O → X) := O.isOpen.isOpenEmbedding_subtypeVal
    apply (hi.continuousAt_iff (x := ⟨x, hx⟩)).mp
    have he : clopenCollapseValue O ∘ (Subtype.val : O → X) = ((↑) : O → OnePoint O) := by
      funext y
      simp [clopenCollapseValue, y.property]
    rw [he]
    exact OnePoint.continuous_coe.continuousAt
  · apply (continuousAt_const (y := (∞ : OnePoint O))).congr_of_eventuallyEq
    filter_upwards [hO.isOpen_compl.mem_nhds hx] with y hy
    change y ∉ O at hy
    simp [clopenCollapseValue, hy]

theorem tendsto_clopenCollapseValue_infty (O : Opens X) :
    Tendsto (clopenCollapseValue O) (coclosedCompact X) (𝓝 (∞ : OnePoint O)) := by
  classical
  apply OnePoint.hasBasis_nhds_infty.tendsto_right_iff.mpr
  intro K hK
  have hi : IsCompact ((Subtype.val : O → X) '' K) := hK.2.image continuous_subtype_val
  filter_upwards [hi.compl_mem_coclosedCompact_of_isClosed hi.isClosed] with x hx
  by_cases hxO : x ∈ O
  · apply Or.inl
    refine ⟨⟨x, hxO⟩, (fun hxK => hx ⟨⟨x, hxO⟩, hxK, rfl⟩), ?_⟩
    simp [clopenCollapseValue, hxO]
  · apply Or.inr
    simp [clopenCollapseValue, hxO]

noncomputable def clopenCompactificationRetraction (O : Opens X) (hO : IsClosed (O : Set X)) :
    C(OnePoint X, OnePoint O) :=
  OnePoint.continuousMapMk ⟨clopenCollapseValue O, continuous_clopenCollapseValue O hO⟩ ∞
    (tendsto_clopenCollapseValue_infty O)

@[simp] theorem clopenCompactificationRetraction_infty (O : Opens X) (hO : IsClosed (O : Set X)) :
    clopenCompactificationRetraction O hO ∞ = ∞ := rfl

@[simp] theorem clopenCompactificationRetraction_coe (O : Opens X) (hO : IsClosed (O : Set X))
    (x : O) : clopenCompactificationRetraction O hO ((x : X) : OnePoint X) = (x : OnePoint O) := by
  change clopenCollapseValue O (x : X) = _
  simp [clopenCollapseValue, x.property]

end AreaDeficit.Surfaces
