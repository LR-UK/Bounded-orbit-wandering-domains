module

public import Mathlib.Topology.Covering.Basic

@[expose] public section

/-! # Coverings from globally extended inverse branches -/

open Function Set Topology

namespace FunctionTheory

/-- A local homeomorphism over a connected base is a covering if every point lies on a
global continuous section. No indexing or quotient of inverse branches is needed. -/
theorem isCoveringMap_of_global_sections
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space E]
    [PreconnectedSpace X] {f : E → X} (hf : IsLocalHomeomorph f)
    (hs : ∀ e : E, ∃ s : C(X, E), f ∘ s = id ∧ s (f e) = e) :
    IsCoveringMap f := by
  classical
  let I := {s : C(X, E) // f ∘ s = id}
  let : TopologicalSpace I := ⊥
  let : DiscreteTopology I := ⟨rfl⟩
  let ev : X × I → E := fun p ↦ p.2.1 p.1
  have hsec (s : I) : IsOpenEmbedding (s.1 : X → E) :=
    hf.isOpenEmbedding_of_comp (by rw [s.2]; exact IsOpenEmbedding.id) s.1.continuous
  have hcont : Continuous ev := continuous_prod_of_discrete_right.mpr fun s ↦ s.1.continuous
  have hopen : IsOpenMap ev := isOpenMap_prod_of_discrete_right.mpr fun s ↦ (hsec s).isOpenMap
  have hbij : Bijective ev := by
    constructor
    · rintro ⟨x, s⟩ ⟨y, t⟩ h
      have hxy : x = y := by
        have h' := congrArg f h
        change f (s.1 x) = f (t.1 y) at h'
        exact (congrFun s.2 x).symm.trans (h'.trans (congrFun t.2 y))
      subst y
      have hst : (s.1 : X → E) = t.1 :=
        (T2Space.isSeparatedMap f).eq_of_comp_eq hf.isLocallyInjective
          s.1.continuous t.1.continuous (s.2.trans t.2.symm) x h
      exact Prod.ext rfl (Subtype.ext (ContinuousMap.coe_injective hst))
    · intro e
      obtain ⟨s, hsf, hse⟩ := hs e
      exact ⟨(f e, ⟨s, hsf⟩), hse⟩
  let H : X × I ≃ₜ E := (Equiv.ofBijective ev hbij).toHomeomorphOfContinuousOpen hcont hopen
  intro x
  apply IsEvenlyCovered.to_isEvenlyCovered_preimage (I := I)
  refine ⟨inferInstance, univ, mem_univ _, isOpen_univ, by simp, ?_, ?_⟩
  · exact (Homeomorph.Set.univ E).trans (H.symm.trans
      ((Homeomorph.Set.univ X).symm.prodCongr (Homeomorph.refl I)))
  · intro e
    change (H.symm e.1).1 = f e.1
    have he := H.apply_symm_apply e.1
    have hproj := congrFun (H.symm e.1).2.2 (H.symm e.1).1
    change f (ev (H.symm e.1)) = (H.symm e.1).1 at hproj
    rw [show ev (H.symm e.1) = e.1 from he] at hproj
    exact hproj.symm

/-- Restricting a local homeomorphism to the full preimage of an open set preserves
the local homeomorphism property. -/
theorem isLocalHomeomorph_restrictPreimage
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} {U : Set X} (hU : IsOpen U) (hc : Continuous f)
    (hf : IsLocalHomeomorphOn f (f ⁻¹' U)) :
    IsLocalHomeomorph (U.restrictPreimage f) := by
  have hi := (hU.preimage hc).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hcomp : IsLocalHomeomorph (f ∘ (Subtype.val : (f ⁻¹' U) → E)) :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr <|
      hf.comp hi.isLocalHomeomorphOn (fun x _ ↦ x.2)
  change IsLocalHomeomorph ((Subtype.val : U → X) ∘ U.restrictPreimage f) at hcomp
  exact hcomp.of_comp hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph
    ((hc.comp continuous_subtype_val).subtype_mk fun x ↦ x.2)

/-- A connected open neighborhood is evenly covered if every preimage point lies on
a continuous inverse branch defined on that entire neighborhood. -/
theorem isEvenlyCovered_of_sections
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space E]
    {f : E → X} {U : Set X} [PreconnectedSpace U]
    (hU : IsOpen U) (hc : Continuous f) (hf : IsLocalHomeomorphOn f (f ⁻¹' U))
    (hs : ∀ e, f e ∈ U → ∃ s : C(U, E),
      (∀ x, f (s x) = x) ∧ ∀ h : f e ∈ U, s ⟨f e, h⟩ = e)
    {x : X} (hx : x ∈ U) : IsEvenlyCovered f x (f ⁻¹' {x}) := by
  have hcover : IsCoveringMap (U.restrictPreimage f) := by
    apply isCoveringMap_of_global_sections (isLocalHomeomorph_restrictPreimage hU hc hf)
    intro e
    obtain ⟨s, hsf, hse⟩ := hs e e.2
    have hmem (x : U) : s x ∈ f ⁻¹' U := by
      change f (s x) ∈ U
      rw [hsf]
      exact x.2
    refine ⟨⟨fun x ↦ ⟨s x, hmem x⟩,
      s.continuous.subtype_mk hmem⟩, ?_, ?_⟩
    · funext x
      exact Subtype.ext (hsf x)
    · exact Subtype.ext (hse e.2)
  exact (IsCoveringMapOn.of_isCoveringMap_restrictPreimage U hU (hU.preimage hc) hcover) x hx

end FunctionTheory
