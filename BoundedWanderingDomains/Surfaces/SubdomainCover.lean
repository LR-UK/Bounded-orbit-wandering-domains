/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.AnalyticSurface
import BoundedWanderingDomains.Surfaces.UniformizationBridge
import BoundedWanderingDomains.Surfaces.PlaneReading
import Mathlib.Analysis.Complex.Liouville

/-! # Disc covers of connected open subdomains

The ambient disc cover excludes the plane and sphere alternatives in the
uniformisation of an open subdomain's universal cover. This supplies covers
for all connected components, without adding hyperbolicity as a hypothesis.
-/

open Set Function Metric RiemannDynamics
open scoped Manifold ContDiff
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]

theorem nonempty_subdomain (p : DiscCover M)
    (U : TopologicalSpace.Opens M) [ConnectedSpace U] : Nonempty (DiscCover U) := by
  classical
  let : IsManifold 𝓘(ℂ) ω M := isManifold_analytic_of_complex
  let : LocallyPathConnectedSpace U := ChartedSpace.locallyPathConnectedSpace ℂ U
  let : PathConnectedSpace U := PathConnectedSpace.of_locallyPathConnectedSpace
  let x : U := Classical.choice (inferInstance : Nonempty U)
  let : T2Space (PathCover x) := t2space_pathCover x
  let : SimplyConnectedSpace (PathCover x) := simplyConnectedSpace_pathCover x
  let : SecondCountableTopology (PathCover x) := secondCountableTopology_pathCover x
  let : LocallyPathConnectedSpace (PathCover x) :=
    ChartedSpace.locallyPathConnectedSpace ℂ (PathCover x)
  let G : PathCover x → M := (Subtype.val : U → M) ∘ pathCoverProj x
  have hproj := (contMDiff_pathCoverProj x).mdifferentiable (by simp)
  have hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G :=
    (mdifferentiable_subtype_val U).comp hproj
  obtain ⟨w,hw⟩ := p.surjective (G (pathCoverBase x))
  obtain ⟨h,_,hfac,hh⟩ := exists_holomorphic_lift
    p.holomorphic p.covering hG (pathCoverBase x) w hw
  let F : PathCover x → ℂ := (Subtype.val : unitDisc → ℂ) ∘ h
  have hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F :=
    (mdifferentiable_subtype_val unitDisc).comp hh
  have hGloc : IsLocalHomeomorph G :=
    U.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph.comp
      (pathCoverProj_isCoveringMap x).isLocalHomeomorph
  have hhloc : IsLocalHomeomorph h := by
    apply IsLocalHomeomorph.of_comp (g := p.projection)
      (f := h) _ p.covering.isLocalHomeomorph hh.continuous
    rw [hfac]
    exact hGloc
  have hFopen : IsOpenMap F :=
    unitDisc.isOpen.isOpenMap_subtype_val.comp hhloc.isOpenMap
  have hnonconstant : ¬ ∃ a : ℂ, F = Function.const (PathCover x) a := by
    rintro ⟨a,ha⟩
    have hrange : range F = {a} := by
      ext z
      constructor
      · rintro ⟨v,rfl⟩
        exact congrFun ha v
      · intro hz
        rw [mem_singleton_iff] at hz
        subst z
        exact ⟨pathCoverBase x, congrFun ha _⟩
    exact not_isOpen_singleton a (hrange ▸ hFopen.isOpen_range)
  rcases uniformization_trichotomy (PathCover x) with hdisc | hplane | hsphere
  · obtain ⟨e⟩ := hdisc
    have hsurj : Surjective (pathCoverProj x) := fun y =>
      ⟨⟨y, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x y)⟩, rfl⟩
    exact ⟨{ projection := pathCoverProj x ∘ e.symm
             holomorphic := hproj.comp (e.symm.mdifferentiable (by simp))
             covering := (pathCoverProj_isCoveringMap x).comp_homeomorph e.symm.toHomeomorph
             surjective := hsurj.comp e.symm.surjective }⟩
  · obtain ⟨e⟩ := hplane
    have hd : Differentiable ℂ (F ∘ e.symm) :=
      (hF.comp (e.symm.mdifferentiable (by simp))).differentiable
    have hb : Bornology.IsBounded (range (F ∘ e.symm)) :=
      (isBounded_ball (x := (0 : ℂ)) (r := 1)).subset (by
        rintro _ ⟨z,rfl⟩
        exact (h (e.symm z)).property)
    obtain ⟨a,ha⟩ := hd.exists_eq_const_of_bounded hb
    apply (hnonconstant ⟨a,?_⟩).elim
    funext z
    simpa only [comp_apply, e.symm_apply_apply, Function.const_apply]
      using congrFun ha (e z)
  · obtain ⟨e⟩ := hsphere
    let : CompactSpace (PathCover x) := e.toHomeomorph.symm.compactSpace
    exact (hnonconstant hF.exists_eq_const_of_compactSpace).elim

end AreaDeficit.Surfaces.DiscCover
