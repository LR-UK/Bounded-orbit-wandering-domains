module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.AmbientComponents
public import BoundedWanderingDomains.Surfaces.SingularEncounters.SourceRestrictionComponents
public import BoundedWanderingDomains.Surfaces.SingularEncounters.EmbeddedDisc

@[expose] public section

/-! # Transport through simultaneous source and ambient restrictions -/

open Set Function Topology

namespace SurfaceDynamics

theorem EmbeddedDisc.inAmbient_carrier
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (O : TopologicalSpace.Opens X) (Q : EmbeddedDisc O) :
    (Q.inAmbient O).carrier = ambientOpen O Q.carrier := by
  apply TopologicalSpace.Opens.ext
  change range (Subtype.val ∘ Q.param) = Subtype.val '' range Q.param
  exact range_comp _ _

namespace LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem inverseComponentSource_fullRestriction_image
    (f : LocalMap X) (hf : Continuous f.map)
    (O V : TopologicalSpace.Opens X) (hVs : (V : Set X) ⊆ f.source)
    (hVO : (V : Set X) ⊆ O)
    (hm : ∀ x : (f.restrictSource V hVs).source, (f.restrictSource V hVs).map x ∈ O)
    (hg : Continuous ((f.restrictSource V hVs).restrictAmbient O hVO hm).map)
    (D : TopologicalSpace.Opens O)
    (hpre : ∀ x : f.source, f.map x ∈ ambientOpen O D → (x : X) ∈ V)
    (a : ((f.restrictSource V hVs).restrictAmbient O hVO hm).source)
    (ha : ((f.restrictSource V hVs).restrictAmbient O hVO hm).map a ∈ D) :
    Subtype.val ''
        (((f.restrictSource V hVs).restrictAmbient O hVO hm).inverseComponentSource hg D a : Set O) =
      (f.inverseComponentSource hf (ambientOpen O D)
        ⟨((a : O) : X), hVs a.2⟩ : Set X) := by
  let r := f.restrictSource V hVs
  let hr := hf.comp (continuous_subtype_val.subtype_mk (fun x : V => hVs x.2))
  let b := (r.restrictAmbientSourceHomeomorph O hVO hm) a
  have hb : r.map b ∈ ambientOpen O D :=
    ⟨(r.restrictAmbient O hVO hm).map a, ha, rfl⟩
  exact (r.inverseComponentSource_restrictAmbient_image hr O hVO hm hg D a ha).trans
    (congrArg (fun A : TopologicalSpace.Opens X => (A : Set X))
      (f.inverseComponentSource_restrictSource_eq hf V hVs (ambientOpen O D) hpre b hb))

theorem componentSingularValues_fullRestriction_subset
    (f : LocalMap X) (hf : Continuous f.map)
    (O V : TopologicalSpace.Opens X) (hVs : (V : Set X) ⊆ f.source)
    (hVO : (V : Set X) ⊆ O)
    (hm : ∀ x : (f.restrictSource V hVs).source, (f.restrictSource V hVs).map x ∈ O)
    (hg : Continuous ((f.restrictSource V hVs).restrictAmbient O hVO hm).map)
    (D : TopologicalSpace.Opens O)
    (hpre : ∀ x : f.source, f.map x ∈ ambientOpen O D → (x : X) ∈ V)
    (a : ((f.restrictSource V hVs).restrictAmbient O hVO hm).source)
    (ha : ((f.restrictSource V hVs).restrictAmbient O hVO hm).map a ∈ D) :
    Subtype.val ''
        ((f.restrictSource V hVs).restrictAmbient O hVO hm).componentSingularValues hg D a ⊆
      f.componentSingularValues hf (ambientOpen O D) ⟨((a : O) : X), hVs a.2⟩ := by
  let r := f.restrictSource V hVs
  let hr := hf.comp (continuous_subtype_val.subtype_mk (fun x : V => hVs x.2))
  let b := (r.restrictAmbientSourceHomeomorph O hVO hm) a
  have hb : r.map b ∈ ambientOpen O D :=
    ⟨(r.restrictAmbient O hVO hm).map a, ha, rfl⟩
  have hsub := r.componentSingularValues_restrictAmbient_subset hr O hVO hm hg D a ha
  have heq := f.componentSingularValues_restrictSource_eq hf V hVs (ambientOpen O D) hpre b hb
  exact hsub.trans heq.subset

end LocalMap
end SurfaceDynamics
