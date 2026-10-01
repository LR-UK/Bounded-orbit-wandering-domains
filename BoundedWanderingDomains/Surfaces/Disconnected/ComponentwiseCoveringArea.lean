module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseAreaDecomposition
public import BoundedWanderingDomains.Surfaces.Disconnected.DomainComponentCovering
public import BoundedWanderingDomains.Surfaces.Disconnected.ConnectedCoveringArea

@[expose] public section

/-! # Area transport for coverings between disconnected open domains -/

open Set Function MeasureTheory TopologicalSpace
open scoped Manifold ENNReal

namespace AreaDeficit.Surfaces.ComponentwiseDiscCover

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [T2Space M] [LocallyCompactSpace M]
  [TopologicalSpace N] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ) 1 N] [MeasurableSpace N] [BorelSpace N]
  [SecondCountableTopology N] [T2Space N] [LocallyCompactSpace N]

theorem domainArea_eq_image_of_component_covering
    (p : ComponentwiseDiscCover M) (q : ComponentwiseDiscCover N)
    (U : Opens M) (V : Opens N) (c : ConnectedComponents U) (d : ConnectedComponents V)
    (G : domainComponent U c → domainComponent V d)
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) (hc : IsCoveringMap G)
    {f : M → N} (hfg : ∀ x : domainComponent U c, f (x : M) = (G x : N))
    {A : Set M} (hA : MeasurableSet A) (him : MeasurableSet (f '' A))
    (hAC : A ⊆ domainComponent U c) (hinj : InjOn f A) :
    p.domainArea U A = q.domainArea V (f '' A) := by
  classical
  let C := domainComponent U c
  let D := domainComponent V d
  let : LocallyCompactSpace C := C.isOpen.locallyCompactSpace
  let : LocallyCompactSpace D := D.isOpen.locallyCompactSpace
  let r : DiscCover C := Classical.choice (p.nonempty_subdomain C)
  let s : DiscCover D := Classical.choice (q.nonempty_subdomain D)
  have himD : f '' A ⊆ D := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hfg ⟨x, hAC hx⟩]
    exact (G ⟨x, hAC hx⟩).property
  have hGi : InjOn G (Subtype.val ⁻¹' A) := by
    intro x hx y hy he
    apply Subtype.ext
    apply hinj hx hy
    rw [hfg x, hfg y]
    exact congrArg Subtype.val he
  have hGA : G '' (Subtype.val ⁻¹' A : Set C) = (Subtype.val ⁻¹' (f '' A) : Set D) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, hfg x⟩
    · rintro ⟨x, hx, hxy⟩
      refine ⟨⟨x, hAC hx⟩, hx, Subtype.ext ?_⟩
      exact (hfg ⟨x, hAC hx⟩).symm.trans hxy
  rw [p.domainArea_domainComponent U c hA hAC,
    q.domainArea_domainComponent V d him himD,
    p.domainArea_eq_hyperbolicArea_preimage_connected C r hA hAC,
    q.domainArea_eq_hyperbolicArea_preimage_connected D s him himD]
  rw [r.hyperbolicArea_eq_image_of_covering s G hG hc
    (hA.preimage continuous_subtype_val.measurable) hGi, hGA]

theorem domainArea_eq_image_of_openDomain_covering_between
    (p : ComponentwiseDiscCover M) (q : ComponentwiseDiscCover N)
    (U : Opens M) (V : Opens N) (F : U → V)
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hc : IsCoveringMap F)
    {f : M → N} (hf : (fun x : U => f x) = (fun x => (F x : N)))
    {A : Set M} (hA : MeasurableSet A) (hAU : A ⊆ U) (hinj : InjOn f A) :
    p.domainArea U A = q.domainArea V (f '' A) := by
  let : Countable (ConnectedComponents U) := countable_ambient_components
  let : PolishSpace M := surfacePolishSpace
  let : PolishSpace N := surfacePolishSpace
  let B : ConnectedComponents U → Set M := fun c => A ∩ domainComponent U c
  have hB : ∀ c, MeasurableSet (B c) := fun c =>
    hA.inter (domainComponent U c).isOpen.measurableSet
  have hsub : ∀ c, B c ⊆ A := fun _ => inter_subset_left
  have hdis : Pairwise (Disjoint on B) :=
    pairwise_disjoint_mono (domainComponent_pairwise_disjoint U) (fun _ => inter_subset_right)
  have hcover : (⋃ c, B c) = A := by
    dsimp only [B]
    rw [← inter_iUnion, iUnion_domainComponent, inter_eq_left.mpr hAU]
  have hfcont : ContinuousOn f U := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun x : U => f x)
    rw [hf]
    exact continuous_subtype_val.comp hF.continuous
  have hfm : ∀ c, MeasurableSet (f '' B c) := fun c =>
    (hB c).image_of_continuousOn_injOn (hfcont.mono ((hsub c).trans hAU))
      (hinj.mono (hsub c))
  have hdisim : Pairwise (Disjoint on fun c => f '' B c) := by
    intro c d hcd
    apply disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, he⟩
    have hxz := hinj (hsub c hx) (hsub d hz) he.symm
    subst z
    exact disjoint_left.mp (hdis hcd) hx hz
  have hlocal : ∀ c, p.domainArea U (B c) = q.domainArea V (f '' B c) := by
    intro c
    obtain ⟨d, G, hG, hGc, hGf⟩ := SurfaceDynamics.covering_domainComponent U V F hF hc c
    apply p.domainArea_eq_image_of_component_covering q U V c d G hG hGc
      (fun x => (congrFun hf ⟨x, domainComponent_le U c x.property⟩).trans (hGf x).symm)
      (hB c) (hfm c) inter_subset_right (hinj.mono (hsub c))
  calc
    p.domainArea U A = ∑' c, p.domainArea U (B c) := by
      rw [← hcover, measure_iUnion hdis hB]
    _ = ∑' c, q.domainArea V (f '' B c) := tsum_congr hlocal
    _ = q.domainArea V (f '' A) := by
      rw [← measure_iUnion hdisim hfm, ← image_iUnion, hcover]

end AreaDeficit.Surfaces.ComponentwiseDiscCover
