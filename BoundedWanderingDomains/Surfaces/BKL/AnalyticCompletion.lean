module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.LocalMapTotalization
public import BoundedWanderingDomains.Surfaces.SubtypeHolomorphic
public import BoundedWanderingDomains.Surfaces.PlaneReading
public import BoundedWanderingDomains.Surfaces.OpenMapping
public import BoundedWanderingDomains.Surfaces.HolomorphicLifting
public import BoundedWanderingDomains.Surfaces.BKL.PuncturedCovers
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseProjection
public import BoundedWanderingDomains.SimplyConnectedFilling
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Compactness.LocallyCompact
public import BoundedWanderingDomains.Surfaces.CompactFilling
public import BoundedWanderingDomains.Surfaces.FiniteFibers
public import BoundedWanderingDomains.Surfaces.SurfaceSingularCovering
public import Mathlib.Topology.DerivedSet
public import BoundedWanderingDomains.Surfaces.SurfaceFilling
public import BoundedWanderingDomains.Surfaces.WanderingDiscShrink

@[expose] public section

section

/-! # Compatible dense analytic extensions of a local surface map

Extensions are confined to the closure of the original source. Agreement on
that dense source makes their values unique wherever their open sources overlap.
-/

open Set Function Filter Topology
open AreaDeficit.Surfaces
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- A holomorphic extension on an open set where the original source is dense.
The values outside this open set are irrelevant. -/
structure DenseExtension (f : LocalMap X) where
  source : TopologicalSpace.Opens X
  value : X → X
  holomorphic : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) value source
  dense : (source : Set X) ⊆ closure (f.source : Set X)
  agrees : ∀ (x : X) (_hx : x ∈ source) (ho : x ∈ f.source),
    value x = f.map ⟨x, ho⟩

namespace DenseExtension

variable {f : LocalMap X}

/-- The original map is one of its dense extensions. -/
noncomputable def original (f : LocalMap X)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map) : DenseExtension f where
  source := f.source
  value := f.totalize
  holomorphic := by
    intro x hx
    apply MDifferentiableAt.mdifferentiableWithinAt
    apply (mdifferentiableAt_subtype_iff (x := ⟨x, hx⟩)).mp
    have he : (fun z : f.source => f.totalize z) = f.map :=
      funext fun z => f.totalize_eq z.property
    rw [he]
    exact hf ⟨x, hx⟩
  dense := subset_closure
  agrees := fun _ _ ho => f.totalize_eq ho

/-- Density is retained on the overlap of two open extension sources. -/
theorem overlap_subset_closure (d e : DenseExtension f) :
    (d.source : Set X) ∩ e.source ⊆
      closure (((d.source : Set X) ∩ e.source) ∩ f.source) := by
  intro x hx
  rw [mem_closure_iff]
  intro W hW hxW
  obtain ⟨y, hyW, hyo⟩ := mem_closure_iff.mp (d.dense hx.1)
    (W ∩ ((d.source : Set X) ∩ e.source))
    (hW.inter (d.source.isOpen.inter e.source.isOpen)) ⟨hxW, hx⟩
  exact ⟨y, hyW.1, hyW.2, hyo⟩

/-- Dense extensions agree on every overlap, by continuity alone. -/
theorem compatible [T2Space X] (d e : DenseExtension f) :
    EqOn d.value e.value ((d.source : Set X) ∩ e.source) := by
  have heq : EqOn d.value e.value
      (((d.source : Set X) ∩ e.source) ∩ f.source) := by
    intro x hx
    exact (d.agrees x hx.1.1 hx.2).trans (e.agrees x hx.1.2 hx.2).symm
  exact heq.of_subset_closure
    (d.holomorphic.continuousOn.mono inter_subset_left)
    (e.holomorphic.continuousOn.mono inter_subset_right)
    inter_subset_left (d.overlap_subset_closure e)

/-- A dense holomorphic extension of an open map remains open. -/
theorem isOpenMap [IsManifold 𝓘(ℂ) 1 X] (d : DenseExtension f)
    (ho : IsOpenMap f.map) : IsOpenMap (fun x : d.source => d.value x) := by
  apply isOpenMap_of_mdifferentiable_of_locally_nonconstant
  · intro x
    exact mdifferentiableAt_subtype_iff.mpr
      ((d.holomorphic x x.property).mdifferentiableAt (d.source.isOpen.mem_nhds x.property))
  · intro x hconst
    obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.mp hconst
    let V : Set X := Subtype.val '' W
    have hVo : IsOpen V := d.source.isOpen.isOpenMap_subtype_val W hWo
    have hxV : (x : X) ∈ V := ⟨x, hxW, rfl⟩
    obtain ⟨y, hyV, hyo⟩ := mem_closure_iff.mp (d.dense x.property) V hVo hxV
    let A : Set f.source := Subtype.val ⁻¹' V
    have hAo : IsOpen A := hVo.preimage continuous_subtype_val
    have hval : ∀ z ∈ A, f.map z = d.value x := by
      intro z hz
      obtain ⟨w, hw, he⟩ := hz
      have hzd : (z : X) ∈ d.source := he ▸ w.property
      rw [← d.agrees z hzd z.property, ← he]
      exact hWsub hw
    have himage : f.map '' A = {d.value x} := by
      apply Subset.antisymm
      · rintro z ⟨w, hw, rfl⟩
        exact hval w hw
      · exact singleton_subset_iff.mpr ⟨⟨y, hyo⟩, hyV, hval ⟨y, hyo⟩ hyV⟩
    exact not_isOpen_singleton_surface (d.value x) (himage ▸ ho A hAo)

end DenseExtension

/-- The union of all dense analytic extension sources. -/
def denseCompletionSource (f : LocalMap X) : TopologicalSpace.Opens X :=
  ⟨{x | ∃ d : DenseExtension f, x ∈ d.source}, by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨d, hx⟩
    exact mem_of_superset (d.source.isOpen.mem_nhds hx) (fun y hy => ⟨d, hy⟩)⟩

theorem source_subset_denseCompletionSource (f : LocalMap X)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map) :
    (f.source : Set X) ⊆ f.denseCompletionSource :=
  fun _ hx => ⟨DenseExtension.original f hf, hx⟩

theorem denseCompletionSource_subset_closure (f : LocalMap X) :
    (f.denseCompletionSource : Set X) ⊆ closure (f.source : Set X) := by
  rintro x ⟨d, hx⟩
  exact d.dense hx

/-- The locally determined extension, set to the identity off its open source. -/
noncomputable def denseCompletionValue (f : LocalMap X) (x : X) : X := by
  classical
  exact if h : x ∈ f.denseCompletionSource then h.choose.value x else x

theorem denseCompletionValue_eq [T2Space X] (f : LocalMap X)
    (d : DenseExtension f) {x : X} (hx : x ∈ d.source) :
    f.denseCompletionValue x = d.value x := by
  have hh : x ∈ f.denseCompletionSource := ⟨d, hx⟩
  rw [denseCompletionValue, dite_eq_left hh]
  exact hh.choose.compatible d ⟨hh.choose_spec, hx⟩

theorem mdifferentiableOn_denseCompletionValue [T2Space X] (f : LocalMap X) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f.denseCompletionValue f.denseCompletionSource := by
  rintro x ⟨d, hx⟩
  apply MDifferentiableAt.mdifferentiableWithinAt
  have hd := (d.holomorphic x hx).mdifferentiableAt (d.source.isOpen.mem_nhds hx)
  apply hd.congr_of_eventuallyEq
  filter_upwards [d.source.isOpen.mem_nhds hx] with y hy
  exact f.denseCompletionValue_eq d hy

/-- The union of all dense extensions is itself a dense extension. -/
noncomputable def denseCompletionExtension [T2Space X] (f : LocalMap X) :
    DenseExtension f where
  source := f.denseCompletionSource
  value := f.denseCompletionValue
  holomorphic := f.mdifferentiableOn_denseCompletionValue
  dense := f.denseCompletionSource_subset_closure
  agrees := by
    rintro x ⟨d, hx⟩ ho
    exact (f.denseCompletionValue_eq d hx).trans (d.agrees x hx ho)

/-- The holomorphic local map obtained by gluing all dense extensions. -/
noncomputable def denseCompletion (f : LocalMap X) : LocalMap X where
  source := f.denseCompletionSource
  map := fun x => f.denseCompletionValue x

theorem isOpenHolomorphic_denseCompletion [T2Space X] [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f) :
    IsOpenHolomorphic f.denseCompletion := by
  refine ⟨(f.denseCompletionExtension).isOpenMap hf.1, ?_⟩
  intro x
  exact mdifferentiableAt_subtype_iff.mpr
    ((f.mdifferentiableOn_denseCompletionValue x x.property).mdifferentiableAt
      (f.denseCompletionSource.isOpen.mem_nhds x.property))

/-- No isolated removable puncture remains outside the union of all dense
extensions. The punctured neighborhood may already use several extensions. -/
theorem mem_denseCompletionSource_of_removable [T2Space X] (f : LocalMap X)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map)
    (V : TopologicalSpace.Opens X) {x : X} (hxV : x ∈ V)
    (hpunct : (V : Set X) \ {x} ⊆ f.denseCompletionSource)
    (g : X → X) (hg : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) g V)
    (heq : EqOn g f.denseCompletionValue ((V : Set X) \ {x})) :
    x ∈ f.denseCompletionSource := by
  classical
  by_contra hx
  have hxo : x ∉ f.source := fun ho => hx (f.source_subset_denseCompletionSource hf ho)
  have hdense : (V : Set X) ⊆ closure (f.source : Set X) := by
    intro y hy
    by_cases hyx : y = x
    · subst y
      by_contra hxc
      let W : Set X := (V : Set X) ∩ (closure (f.source : Set X))ᶜ
      have hWo : IsOpen W := V.isOpen.inter isClosed_closure.isOpen_compl
      have hW : W = {x} := by
        apply Subset.antisymm
        · intro z hz
          by_contra hzx
          exact hz.2 (f.denseCompletionSource_subset_closure (hpunct ⟨hz.1, hzx⟩))
        · exact singleton_subset_iff.mpr ⟨hxV, hxc⟩
      have hopen : IsOpen ({x} : Set X) := hW ▸ hWo
      have himage := (chartAt ℂ x).isOpen_image_of_subset_source hopen
        (singleton_subset_iff.mpr (mem_chart_source ℂ x))
      rw [image_singleton] at himage
      exact not_isOpen_singleton (chartAt ℂ x x) himage
    · exact f.denseCompletionSource_subset_closure (hpunct ⟨hy, hyx⟩)
  let d : DenseExtension f :=
    { source := V
      value := g
      holomorphic := hg
      dense := hdense
      agrees := by
        intro y hy ho
        have hyx : y ≠ x := fun he => hxo (he ▸ ho)
        exact (heq ⟨hy, hyx⟩).trans
          ((f.denseCompletionExtension).agrees y
            (f.source_subset_denseCompletionSource hf ho) ho) }
  exact hx ⟨d, hxV⟩

end SurfaceDynamics.LocalMap

end

section

/-! # Removable points described by holomorphic parameters

A holomorphic parameter across a finite covering end supplies a removable
extension of the local map. Maximal dense completion already contains its
centre. No transcendence assumption is used.
-/

open Set Function
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X]

/-- A removable finite covering end, expressed in a holomorphic source
parameter, belongs to the completed source. -/
theorem mem_denseCompletionSource_of_parametrized_extension
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M]
    (f : LocalMap X) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map)
    (e : OpenPartialHomeomorph M X)
    (he : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source)
    {b : M} (hb : b ∈ e.source) (v : M → X)
    (hv : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) v e.source)
    (hpunct : ∀ z ∈ e.source, z ≠ b → e z ∈ f.denseCompletionSource)
    (hvalue : ∀ z ∈ e.source, z ≠ b → f.denseCompletionValue (e z) = v z) :
    e b ∈ f.denseCompletionSource := by
  let V : TopologicalSpace.Opens X := ⟨e.target, e.open_target⟩
  apply f.mem_denseCompletionSource_of_removable hf V (e.map_source hb)
    (g := v ∘ e.symm)
  · rintro x ⟨hx, hxb⟩
    have hne : e.symm x ≠ b := by
      intro hh
      apply hxb
      change x = e b
      rw [← e.right_inv hx, hh]
    change x ∈ f.denseCompletionSource
    simpa only [e.right_inv hx] using hpunct (e.symm x) (e.map_target hx) hne
  · exact hv.comp (AreaDeficit.Surfaces.mdifferentiableOn_symm he) e.mapsTo_symm
  · rintro x ⟨hx, hxb⟩
    have hne : e.symm x ≠ b := by
      intro hh
      apply hxb
      change x = e b
      rw [← e.right_inv hx, hh]
    have hh := hvalue (e.symm x) (e.map_target hx) hne
    simpa only [comp_apply, e.right_inv hx] using hh.symm

/-- A holomorphic local homeomorphism at a puncture provides the parameter
needed for maximal removable completion. -/
theorem mem_denseCompletionSource_of_local_parameter
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M]
    (f : LocalMap X) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map)
    {u v : M → X} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u)
    (hl : IsLocalHomeomorph u) (hv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) v) (b : M)
    (hpunct : ∀ z, z ≠ b → u z ∈ f.denseCompletionSource)
    (hvalue : ∀ z, z ≠ b → f.denseCompletionValue (u z) = v z) :
    u b ∈ f.denseCompletionSource := by
  obtain ⟨e, heb, heu⟩ := hl b
  have he : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source := by
    rw [← heu]
    exact hu.mdifferentiableOn
  have hb := f.mem_denseCompletionSource_of_parametrized_extension hf e he heb v
    hv.mdifferentiableOn (fun z _ hz => heu ▸ hpunct z hz)
    (fun z _ hz => heu ▸ hvalue z hz)
  simpa only [← heu] using hb

end SurfaceDynamics.LocalMap

end

section

/-! # Projecting a filled covering component into the completed source -/

open Set Function Metric Topology
open scoped Manifold Topology
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL.FilledPuncturedCover

variable {A : TopologicalSpace.Opens ℂ} {p : A → puncturedUnitDisc}

noncomputable def discMap (F : FilledPuncturedCover A p) : unitDisc → unitDisc :=
  fun z => ⟨F.extension z, F.mapsTo z.2⟩

theorem mdifferentiable_discMap (F : FilledPuncturedCover A p) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F.discMap := by
  apply (mdifferentiable_subtypeVal_comp_iff unitDisc _).mp
  intro z
  apply mdifferentiableAt_subtype_iff.mpr
  exact (F.holomorphic.differentiableAt (isOpen_ball.mem_nhds z.2)).mdifferentiableAt

theorem isOpenEmbedding_discMap (F : FilledPuncturedCover A p) :
    IsOpenEmbedding F.discMap := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap F.mdifferentiable_discMap.continuous
  · intro x y hxy
    apply Subtype.ext
    exact F.injective x.2 y.2 (congrArg Subtype.val hxy)
  · exact (TauCeti.isOpenMap_restrict_of_differentiableOn_of_injOn isOpen_ball
      F.holomorphic F.injective).subtype_mk (fun z => F.mapsTo z.2)

theorem discMap_eq_parameter (F : FilledPuncturedCover A p)
    (hA : (A : Set ℂ) ⊆ ball 0 1) (z : puncturedUnitDisc) :
    F.discMap ⟨z, z.2.1⟩ = ⟨F.parameter z, hA (F.parameter z).2⟩ :=
  Subtype.ext (F.agrees z)

/-- The finite end of a covering component lies in the maximal dense
completion, once its value has a holomorphic extension through the puncture.
The ambient projection need only be a holomorphic local homeomorphism. -/
theorem projected_filling_subset_denseCompletion
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map)
    (F : FilledPuncturedCover A p) (hA : (A : Set ℂ) ⊆ ball 0 1)
    {q v : unitDisc → X} (hq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) q)
    (hql : IsLocalHomeomorph q) (hv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) v)
    (hsource : ∀ a : A, q ⟨a, hA a.2⟩ ∈ f.denseCompletionSource)
    (hvalue : ∀ z : puncturedUnitDisc,
      f.denseCompletionValue (q ⟨F.parameter z, hA (F.parameter z).2⟩) = v ⟨z, z.2.1⟩) :
    ∀ z : unitDisc, q (F.discMap z) ∈ f.denseCompletionSource := by
  let b : unitDisc := ⟨0, mem_ball_self zero_lt_one⟩
  have hpunct (z : unitDisc) (hz : z ≠ b) : q (F.discMap z) ∈ f.denseCompletionSource := by
    have hz0 : (z : ℂ) ≠ 0 := fun he => hz (Subtype.ext he)
    let w : puncturedUnitDisc := ⟨z, z.2, hz0⟩
    have he := F.discMap_eq_parameter hA w
    change F.discMap z = _ at he
    rw [he]
    exact hsource (F.parameter w)
  have hvalues (z : unitDisc) (hz : z ≠ b) :
      f.denseCompletionValue (q (F.discMap z)) = v z := by
    have hz0 : (z : ℂ) ≠ 0 := fun he => hz (Subtype.ext he)
    let w : puncturedUnitDisc := ⟨z, z.2, hz0⟩
    have he := F.discMap_eq_parameter hA w
    change F.discMap z = _ at he
    rw [he]
    exact hvalue w
  have hcentre : q (F.discMap b) ∈ f.denseCompletionSource :=
    f.mem_denseCompletionSource_of_local_parameter hf
      (hq.comp F.mdifferentiable_discMap)
      (hql.comp F.isOpenEmbedding_discMap.isLocalHomeomorph) hv b hpunct hvalues
  intro z
  by_cases hz : z = b
  · simpa only [hz] using hcentre
  · exact hpunct z hz

end SurfaceDynamics.BKL.FilledPuncturedCover

end

section

/-! # Compact fillings over a once-punctured regular-value disc stay in the completed source

This proves source containment before applying the open-map filling lemma.
The covering component is taken in the ambient universal disc, where a finite
covering end is bounded and therefore removable.
-/

open Set Function Metric Topology
open scoped Manifold
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

theorem exists_simplyConnected_cover_filling_in_source
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map)
    (A : TopologicalSpace.Opens ℂ) [ConnectedSpace A]
    {p : A → puncturedUnitDisc} (hp : IsCoveringMap p)
    (hph : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) (hA : (A : Set ℂ) ⊆ ball 0 1)
    {q t : unitDisc → X} (hq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) q)
    (hql : IsLocalHomeomorph q) (ht : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) t)
    (hsource : ∀ a : A, q ⟨a, hA a.2⟩ ∈ f.denseCompletionSource)
    (hvalue : ∀ a : A, f.denseCompletionValue (q ⟨a, hA a.2⟩) =
      t ⟨p a, (p a).2.1⟩) :
    ∃ V : Set ℂ, IsOpen V ∧ IsSimplyConnected V ∧ (A : Set ℂ) ⊆ V ∧
      V ⊆ ball 0 1 ∧ ∀ z (_hz : z ∈ V) (hzd : z ∈ ball 0 1),
        q ⟨z, hzd⟩ ∈ f.denseCompletionSource := by
  rcases simplyConnected_or_filledPuncturedCover A hp hph hA with hsc | hfill
  · exact ⟨A, A.isOpen, hsc, subset_rfl, hA, fun z hz _ => hsource ⟨z, hz⟩⟩
  · obtain ⟨F⟩ := hfill
    have hfilled := F.projected_filling_subset_denseCompletion f hf hA hq hql
      (ht.comp (mdifferentiable_discPower F.degree F.degree_pos)) hsource (fun z => by
        rw [hvalue]
        apply congrArg t
        exact Subtype.ext (F.map_parameter z))
    refine ⟨insert (F.extension 0) (A : Set ℂ), F.open_filling,
      F.simplyConnected_filling, subset_insert _ _, ?_, ?_⟩
    · rw [← F.image_eq]
      exact F.mapsTo.image_subset
    · intro z hz hzd
      rw [← F.image_eq] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact hfilled ⟨w, hw⟩

theorem projected_compactFill_subset_source
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map)
    (A : TopologicalSpace.Opens ℂ) [ConnectedSpace A]
    {p : A → puncturedUnitDisc} (hp : IsCoveringMap p)
    (hph : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) (hA : (A : Set ℂ) ⊆ ball 0 1)
    {q t : unitDisc → X} (hq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) q)
    (hql : IsLocalHomeomorph q) (ht : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) t)
    (hsource : ∀ a : A, q ⟨a, hA a.2⟩ ∈ f.denseCompletionSource)
    (hvalue : ∀ a : A, f.denseCompletionValue (q ⟨a, hA a.2⟩) =
      t ⟨p a, (p a).2.1⟩)
    {K : Set ℂ} (hK : IsCompact K) (hKA : K ⊆ A) :
    ComplexApproximation.fill K ⊆ ball 0 1 ∧
      ∀ z ∈ ComplexApproximation.fill K, ∀ hzd : z ∈ ball 0 1,
        q ⟨z, hzd⟩ ∈ f.denseCompletionSource := by
  obtain ⟨V, hVo, hVsc, hAV, hVD, hsourceV⟩ :=
    exists_simplyConnected_cover_filling_in_source f hf A hp hph hA hq hql ht hsource hvalue
  have hfill : ComplexApproximation.fill K ⊆ V :=
    AreaDeficit.fill_subset_of_isSimplyConnected hK hVo hVsc (hKA.trans hAV)
  exact ⟨hfill.trans hVD, fun z hz hzd => hsourceV z (hfill hz) hzd⟩

end SurfaceDynamics.BKL

end

section

/-! # Filling a connected compact set in the full lifted preimage -/

open Set Function Metric Topology
open scoped Manifold
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

theorem projected_compactFill_of_lifted_cover
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map)
    (q : DiscCovering X) {t : unitDisc → X} (ht : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) t)
    (B : TopologicalSpace.Opens unitDisc) (F : B → puncturedUnitDisc)
    (hF : IsCoveringMap F) (hFh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hsource : ∀ z : B, q.projection z ∈ f.denseCompletionSource)
    (hvalue : ∀ z : B, f.denseCompletionValue (q.projection z) = t ⟨F z, (F z).2.1⟩)
    {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K)
    (hKB : K ⊆ (Subtype.val : unitDisc → ℂ) '' (B : Set unitDisc)) :
    ComplexApproximation.fill K ⊆ ball 0 1 ∧
      ∀ z ∈ ComplexApproximation.fill K, ∀ hzd : z ∈ ball 0 1,
        q.projection ⟨z, hzd⟩ ∈ f.denseCompletionSource := by
  let i : B → ℂ := (Subtype.val : unitDisc → ℂ) ∘ (Subtype.val : B → unitDisc)
  have hi : IsOpenEmbedding i := unitDisc.isOpen.isOpenEmbedding_subtypeVal.comp
    B.isOpen.isOpenEmbedding_subtypeVal
  have hih : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) i :=
    (mdifferentiable_subtype_val unitDisc).comp (mdifferentiable_subtype_val B)
  have hKr : K ⊆ range i := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hKB hz
    exact ⟨⟨w, hw⟩, rfl⟩
  have hpre : IsConnected (i ⁻¹' K) :=
    hKc.preimage_of_isOpenMap hi.injective hi.isOpenMap hKr
  obtain ⟨b₀, hb₀⟩ := hpre.nonempty
  have hKC : i ⁻¹' K ⊆ connectedComponent b₀ := hpre.subset_connectedComponent hb₀
  obtain ⟨A, hA, hAc, r, hr, hrh, hri⟩ :=
    exists_planar_connected_cover_component hF hFh hi hih b₀
  let : ConnectedSpace A := hAc
  have hAD : (A : Set ℂ) ⊆ ball 0 1 := by
    rw [hA]
    rintro _ ⟨b, _, rfl⟩
    exact (b : unitDisc).2
  have hKA : K ⊆ A := by
    intro z hz
    obtain ⟨b, rfl⟩ := hKr hz
    rw [hA]
    exact ⟨b, hKC hz, rfl⟩
  have hsA : ∀ a : A, q.projection ⟨a, hAD a.2⟩ ∈ f.denseCompletionSource := by
    intro a
    have haA : (a : ℂ) ∈ i '' connectedComponent b₀ := by
      rw [← hA]
      exact a.2
    obtain ⟨b, _, he⟩ := haA
    have heD : (⟨a, hAD a.2⟩ : unitDisc) = (b : unitDisc) := Subtype.ext he.symm
    rw [heD]
    exact hsource b
  have hvA : ∀ a : A, f.denseCompletionValue (q.projection ⟨a, hAD a.2⟩) =
      t ⟨r a, (r a).2.1⟩ := by
    intro a
    have haA : (a : ℂ) ∈ i '' connectedComponent b₀ := by
      rw [← hA]
      exact a.2
    obtain ⟨b, hb, he⟩ := haA
    have hbA : i b ∈ A := he.symm ▸ a.2
    have ha : a = (⟨i b, hbA⟩ : A) := Subtype.ext he.symm
    rw [ha, hri b hb hbA]
    exact hvalue b
  exact projected_compactFill_subset_source f hf A hr hrh hAD q.holomorphic
    q.covering.isLocalHomeomorph ht hsA hvA hK hKA

end SurfaceDynamics.BKL

end

section

/-! # Covering values cannot acquire isolated new preimages in a dense extension

This is the topological singular-value bookkeeping needed for removable
completion. Compact neighborhoods prevent a covering sheet from leaving the
neighborhood through its frontier.
-/

open Set Function Topology

namespace SurfaceDynamics.BKL

variable {E Y Z : Type*} [TopologicalSpace E] [TopologicalSpace Y]
  [TopologicalSpace Z] [T2Space Y] [LocallyCompactSpace Y]
  [T2Space Z] [LocallyConnectedSpace Z]

/-- Over an evenly covered value, a continuous dense extension with an isolated
fibre has no additional point. Neither holomorphy nor a transcendental
singularity assumption enters this topological assertion. -/
theorem mem_range_of_evenlyCovered_of_discrete_fibre
    {i : E → Y} (hi : Continuous i) (hdense : DenseRange i)
    {p : E → Z} {g : Y → Z} (hg : Continuous g) (hcomp : g ∘ i = p)
    {a : Y} (hfib : IsDiscrete (g ⁻¹' {g a}))
    (hcov : IsEvenlyCovered p (g a) (p ⁻¹' {g a})) : a ∈ range i := by
  classical
  obtain ⟨A, hAo, hA⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hfib a rfl
  have haA : a ∈ A := (hA.symm ▸ mem_singleton a).1
  have hiso : ∀ y ∈ A, g y = g a → y = a := by
    intro y hy he
    have hh : y ∈ A ∩ g ⁻¹' {g a} := ⟨hy, he⟩
    exact mem_singleton_iff.mp (hA ▸ hh)
  obtain ⟨K, hK, haK, hKA⟩ := exists_compact_subset hAo haA
  let D := interior K
  have hDo : IsOpen D := isOpen_interior
  have hDK : closure D ⊆ K := closure_minimal interior_subset hK.isClosed
  have hboundary : IsCompact (frontier D) :=
    hK.of_isClosed_subset isClosed_frontier (frontier_subset_closure.trans hDK)
  have hga : g a ∉ g '' frontier D := by
    rintro ⟨b, hb, he⟩
    have hba : b = a := hiso b (hKA (hDK hb.1)) he
    subst b
    exact hb.2 (hDo.interior_eq.symm ▸ haK)
  obtain ⟨_, T, haT, hTo, _, H, hH⟩ := hcov
  let N := connectedComponentIn (T \ g '' frontier D) (g a)
  have haN : g a ∈ N := mem_connectedComponentIn ⟨haT, hga⟩
  have hNo : IsOpen N := (hTo.sdiff (hboundary.image hg).isClosed).connectedComponentIn
  have hNc : IsConnected N := isConnected_connectedComponentIn_iff.mpr ⟨haT, hga⟩
  have hNsub : N ⊆ T \ g '' frontier D := connectedComponentIn_subset _ _
  have hnear : IsOpen (D ∩ g ⁻¹' N) := hDo.inter (hNo.preimage hg)
  obtain ⟨y, hy, w, rfl⟩ := mem_closure_iff.mp (hdense a)
    (D ∩ g ⁻¹' N) hnear ⟨haK, haN⟩
  have hpw : p w ∈ N := by
    rw [← hcomp]
    exact hy.2
  let wT : p ⁻¹' T := ⟨w, (hNsub hpw).1⟩
  let j := (H wT).2
  let s : N → E := fun z => (H.symm (⟨z, (hNsub z.property).1⟩, j)).val
  have hs : Continuous s := by
    dsimp [s]
    fun_prop
  have hps : ∀ z : N, p (s z) = z := by
    intro z
    have hh := hH (H.symm (⟨z, (hNsub z.property).1⟩, j))
    simpa only [Homeomorph.apply_symm_apply] using hh.symm
  have hsw : s ⟨p w, hpw⟩ = w := by
    have he : (⟨p w, (hNsub hpw).1⟩, j) = H wT := by
      apply Prod.ext
      · exact Subtype.ext (hH wT).symm
      · rfl
    dsimp only [s]
    rw [he, H.symm_apply_apply]
  let C := range (i ∘ s)
  let : ConnectedSpace N := Subtype.connectedSpace hNc
  have hCc : IsPreconnected C := isPreconnected_range (hi.comp hs)
  have havoid : Disjoint C (frontier D) := by
    apply disjoint_left.mpr
    rintro b ⟨z, rfl⟩ hb
    have he : g (i (s z)) = z := by
      change (g ∘ i) (s z) = z
      rw [hcomp]
      exact hps z
    exact (hNsub z.property).2 ⟨i (s z), hb, he⟩
  have hmeet : (C ∩ D).Nonempty := by
    refine ⟨i w, ?_, hy.1⟩
    exact ⟨⟨p w, hpw⟩, congrArg i hsw⟩
  have hCD : C ⊆ D :=
    AreaDeficit.Surfaces.preconnected_subset_open_of_avoids_frontier hCc hDo havoid hmeet
  let z : N := ⟨g a, haN⟩
  have hiz : i (s z) ∈ D := hCD (mem_range_self z)
  refine ⟨s z, hiso _ (hKA (interior_subset hiz)) ?_⟩
  change (g ∘ i) (s z) = g a
  rw [hcomp]
  exact hps z

end SurfaceDynamics.BKL

end

section

/-! # Singular values of the dense analytic completion -/

open Set Function Topology
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The original source embeds into the completed source. -/
noncomputable def denseCompletionInclusion (f : LocalMap X)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map) : f.source → f.denseCompletion.source :=
  fun x => ⟨x, f.source_subset_denseCompletionSource hf x.property⟩

theorem continuous_denseCompletionInclusion (f : LocalMap X)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map) : Continuous (f.denseCompletionInclusion hf) := by
  exact continuous_subtype_val.subtype_mk _

theorem denseRange_denseCompletionInclusion (f : LocalMap X)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map) : DenseRange (f.denseCompletionInclusion hf) := by
  intro a
  rw [mem_closure_iff]
  intro W hWo haW
  have hVo : IsOpen (Subtype.val '' W : Set X) :=
    f.denseCompletionSource.isOpen.isOpenMap_subtype_val W hWo
  obtain ⟨y, ⟨z, hzW, hzy⟩, hyo⟩ :=
    mem_closure_iff.mp (f.denseCompletionSource_subset_closure a.property)
      (Subtype.val '' W) hVo ⟨a, haW, rfl⟩
  have he : f.denseCompletionInclusion hf ⟨y, hyo⟩ = z := Subtype.ext hzy.symm
  exact ⟨z, hzW, ⟨⟨y, hyo⟩, he⟩⟩

theorem denseCompletion_map_inclusion [T2Space X] (f : LocalMap X)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map) :
    f.denseCompletion.map ∘ f.denseCompletionInclusion hf = f.map := by
  funext x
  exact f.denseCompletionExtension.agrees x
    (f.source_subset_denseCompletionSource hf x.property) x.property

/-- Every added point lies over a singular value of the original map. -/
theorem added_image_mem_singularValues [T2Space X] [LocallyCompactSpace X]
    [IsManifold 𝓘(ℂ) 1 X] (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (x : f.denseCompletion.source) (hx : (x : X) ∉ f.source) :
    f.denseCompletion.map x ∈ f.singularValues := by
  classical
  let : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  let : LocallyCompactSpace f.denseCompletion.source :=
    f.denseCompletion.source.isOpen.locallyCompactSpace
  by_contra hs
  have hreg : f.denseCompletion.map x ∈ f.regularValues := by
    simpa only [singularValues, mem_compl_iff, not_not] using hs
  obtain ⟨W, _, hxW, hcov⟩ := hreg
  have hg := f.isOpenHolomorphic_denseCompletion hf
  have hdis : IsDiscrete
      (f.denseCompletion.map ⁻¹' {f.denseCompletion.map x}) :=
    isDiscrete_fiber_of_isOpenMap_of_mdifferentiable hg.1 hg.2 _
  have hxrange := BKL.mem_range_of_evenlyCovered_of_discrete_fibre
    (f.continuous_denseCompletionInclusion hf.2)
    (f.denseRange_denseCompletionInclusion hf.2) hg.2.continuous
    (f.denseCompletion_map_inclusion hf.2) hdis (hcov _ hxW)
  obtain ⟨a, ha⟩ := hxrange
  exact hx (congrArg Subtype.val ha ▸ a.property)

/-- Regular values of the original map remain regular after dense completion. -/
theorem regularValues_subset_denseCompletion [T2Space X] [LocallyCompactSpace X]
    [IsManifold 𝓘(ℂ) 1 X] (f : LocalMap X) (hf : IsOpenHolomorphic f) :
    f.regularValues ⊆ f.denseCompletion.regularValues := by
  classical
  intro y hy
  obtain ⟨W, hWo, hyW, hcov⟩ := hy
  let g := f.denseCompletion
  have hgold : ∀ (x : g.source) (ho : (x : X) ∈ f.source),
      f.map ⟨x, ho⟩ = g.map x := fun x ho =>
    (f.denseCompletionExtension.agrees x x.property ho).symm
  have hpre : ∀ x : g.source, g.map x ∈ W → (x : X) ∈ f.source := by
    intro x hxW
    by_contra hxo
    exact f.added_image_mem_singularValues hf x hxo ⟨W, hWo, hxW, hcov⟩
  have hinc : ∀ a : f.source, g.map (f.denseCompletionInclusion hf.2 a) = f.map a :=
    fun a => congrFun (f.denseCompletion_map_inclusion hf.2) a
  let e : (g.map ⁻¹' W) ≃ₜ (f.map ⁻¹' W) :=
    { toFun := fun x =>
        ⟨⟨((x : g.source) : X), hpre x x.property⟩, by
          change f.map ⟨((x : g.source) : X), hpre x x.property⟩ ∈ W
          rw [hgold x (hpre x x.property)]
          exact x.property⟩
      invFun := fun x =>
        ⟨f.denseCompletionInclusion hf.2 x, by
          change g.map (f.denseCompletionInclusion hf.2 x) ∈ W
          rw [hinc]
          exact x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by
        exact ((f.continuous_denseCompletionInclusion hf.2).comp
          continuous_subtype_val).subtype_mk _ }
  have hc := hcov.isCoveringMap_restrictPreimage.comp_homeomorph e
  have heq : W.restrictPreimage f.map ∘ e = W.restrictPreimage g.map := by
    funext x
    exact Subtype.ext (hgold x (hpre x x.property))
  rw [heq] at hc
  have hg := f.isOpenHolomorphic_denseCompletion hf
  have hgc : IsCoveringMapOn g.map W :=
    IsCoveringMapOn.of_isCoveringMap_restrictPreimage W hWo
      (hWo.preimage hg.2.continuous) hc
  exact ⟨W, hWo, hyW, hgc⟩

/-- Dense completion introduces no singular values. -/
theorem singularValues_denseCompletion_subset [T2Space X] [LocallyCompactSpace X]
    [IsManifold 𝓘(ℂ) 1 X] (f : LocalMap X) (hf : IsOpenHolomorphic f) :
    f.denseCompletion.singularValues ⊆ f.singularValues :=
  compl_subset_compl.mpr (f.regularValues_subset_denseCompletion hf)

/-- In particular, completion cannot enlarge the derived singular set. -/
theorem derived_singularValues_denseCompletion_subset [T2Space X] [LocallyCompactSpace X]
    [IsManifold 𝓘(ℂ) 1 X] (f : LocalMap X) (hf : IsOpenHolomorphic f) :
    derivedSet f.denseCompletion.singularValues ⊆ derivedSet f.singularValues :=
  derivedSet_mono _ _ (f.singularValues_denseCompletion_subset hf)

/-- Added points over a fixed finite collection of original singular values
form a discrete set in the completed source. -/
theorem isDiscrete_added_points_over_finite [T2Space X] [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f) {E : Set X} (hE : E.Finite)
    {A : Set f.denseCompletion.source}
    (hA : ∀ x ∈ A, f.denseCompletion.map x ∈ E) : IsDiscrete A := by
  have hg := f.isOpenHolomorphic_denseCompletion hf
  have hpre : IsDiscrete (f.denseCompletion.map ⁻¹' E) :=
    hE.isDiscrete.preimage' hg.2.continuous.continuousOn
      (fun y => isDiscrete_fiber_of_isOpenMap_of_mdifferentiable hg.1 hg.2 y)
  exact hpre.mono hA

/-- On a compact region, finite singular-value control makes the set of
added points finite. No global discreteness of all added points is assumed. -/
theorem finite_added_points_in_compact [T2Space X] [LocallyCompactSpace X]
    [IsManifold 𝓘(ℂ) 1 X] (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {K : Set f.denseCompletion.source} (hK : IsCompact K)
    {E : Set X} (hE : E.Finite)
    (hKE : ∀ x ∈ K, f.denseCompletion.map x ∈ f.singularValues →
      f.denseCompletion.map x ∈ E) :
    (K ∩ {x : f.denseCompletion.source | (x : X) ∉ f.source}).Finite := by
  have hg := f.isOpenHolomorphic_denseCompletion hf
  have hsub : K ∩ {x : f.denseCompletion.source | (x : X) ∉ f.source} ⊆
      K ∩ f.denseCompletion.map ⁻¹' E := by
    rintro x ⟨hxK, hxo⟩
    exact ⟨hxK, hKE x hxK (f.added_image_mem_singularValues hf x hxo)⟩
  apply Set.Finite.subset _ hsub
  exact (hK.inter_right (hE.isClosed.preimage hg.2.continuous)).finite
    (f.isDiscrete_added_points_over_finite hf hE (fun _ hx => hx.2))

end SurfaceDynamics.LocalMap

end

section

/-! # Filling over regular punctured discs for a locally defined map -/

open Set Function Metric Topology
open scoped Manifold
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

theorem projected_fill_subset_denseCompletion_of_regular_puncturedDisc
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (q : DiscCovering X)
    {t : unitDisc → X} (ht : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) t) (hte : IsOpenEmbedding t)
    (hreg : ∀ z : puncturedUnitDisc, t ⟨z, z.2.1⟩ ∈ f.regularValues)
    {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K) (hKD : K ⊆ ball 0 1)
    (hsource : ∀ z ∈ K, ∀ hzd : z ∈ ball 0 1, q.projection ⟨z, hzd⟩ ∈ f.source)
    (himage : ∀ z ∈ K, ∀ hzd : z ∈ ball 0 1,
      f.totalize (q.projection ⟨z, hzd⟩) ∈
        range (fun w : puncturedUnitDisc => t ⟨w, w.2.1⟩)) :
    ComplexApproximation.fill K ⊆ ball 0 1 ∧
      ∀ z ∈ ComplexApproximation.fill K, ∀ hzd : z ∈ ball 0 1,
        q.projection ⟨z, hzd⟩ ∈ f.denseCompletionSource := by
  let g := f.denseCompletion
  have hg := f.isOpenHolomorphic_denseCompletion hf
  obtain ⟨B, F, hF, hFh, hsrc, hval, hfull⟩ := exists_lifted_regular_cover g hg.2 q ht hte
    (fun z => f.regularValues_subset_denseCompletion hf (hreg z))
  have hgeq {x : X} (hx : x ∈ f.source) : g.totalize x = f.totalize x := by
    rw [g.totalize_eq (f.source_subset_denseCompletionSource hf.2 hx), f.totalize_eq hx]
    exact f.denseCompletionExtension.agrees x
      (f.source_subset_denseCompletionSource hf.2 hx) hx
  have hKB : K ⊆ (Subtype.val : unitDisc → ℂ) '' (B : Set unitDisc) := by
    intro z hz
    have hzd := hKD hz
    have hzs := hsource z hz hzd
    refine ⟨⟨z, hzd⟩, ?_, rfl⟩
    apply hfull
    · exact f.source_subset_denseCompletionSource hf.2 hzs
    · rw [hgeq hzs]
      exact himage z hz hzd
  apply projected_compactFill_of_lifted_cover f hf.2 q ht B F hF hFh hsrc _ hK hKc hKB
  intro z
  have hh := hval z
  rw [g.totalize_eq (hsrc z)] at hh
  exact hh

end SurfaceDynamics.BKL

end

section

/-! # Inverse charts of an ambient disc cover over simply connected domains -/

open Set Function Topology
open scoped Manifold
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

theorem exists_cover_inverse_chart
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (q : DiscCovering X) (W : TopologicalSpace.Opens X) [SimplyConnectedSpace W]
    (x₀ : W) (hx₀ : (x₀ : X) ∈ range q.projection) :
    ∃ e : OpenPartialHomeomorph X ℂ, e.source = W ∧
      e.target ⊆ unitDisc ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source ∧
      ∀ x (_hx : x ∈ e.source), ∀ heD : e x ∈ unitDisc,
        q.projection ⟨e x, heD⟩ = x := by
  let : LocallyPathConnectedSpace W := ChartedSpace.locallyPathConnectedSpace ℂ W
  obtain ⟨z₀, hz₀⟩ := hx₀
  obtain ⟨H, _, hH, hHh⟩ := exists_holomorphic_lift q.holomorphic q.covering
    (mdifferentiable_subtype_val W) x₀ z₀ hz₀
  have hHe : IsOpenEmbedding H := q.covering.isLocalHomeomorph.isOpenEmbedding_of_comp
    (hH.symm ▸ W.isOpen.isOpenEmbedding_subtypeVal) hHh.continuous
  let G : W → ℂ := (Subtype.val : unitDisc → ℂ) ∘ H
  have hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G :=
    (mdifferentiable_subtype_val unitDisc).comp hHh
  have hGe : IsOpenEmbedding G := unitDisc.isOpen.isOpenEmbedding_subtypeVal.comp hHe
  let i := W.openPartialHomeomorphSubtypeCoe (inferInstance : Nonempty W)
  let j := hGe.toOpenPartialHomeomorph G
  let e : OpenPartialHomeomorph X ℂ := i.symm.trans j
  have hes : e.source = (W : Set X) := by
    simp [e, i, j]
  have het : e.target ⊆ unitDisc := by
    intro z hz
    have hzj : z ∈ j.target := hz.1
    have hzj' : z ∈ range G := by simpa [j] using hzj
    obtain ⟨w, rfl⟩ := hzj'
    exact (H w).2
  have hi : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) i i.source :=
    (mdifferentiable_subtype_val W).mdifferentiableOn
  have heh : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source := by
    intro x hx
    have hxW : x ∈ W := by rwa [hes] at hx
    have hxi : x ∈ i.target := by simpa [i] using hxW
    have hdi := ((mdifferentiableOn_symm hi) x hxi).mdifferentiableAt
      (i.open_target.mem_nhds hxi)
    exact ((hG (i.symm x)).comp x hdi).mdifferentiableWithinAt
  refine ⟨e, hes, het, heh, ?_⟩
  intro x hx heD
  have hxW : x ∈ W := by rwa [hes] at hx
  have hei : i.symm x = (⟨x, hxW⟩ : W) := by
    apply Subtype.ext
    exact i.right_inv (by simpa [i] using hxW)
  have heval : (⟨e x, heD⟩ : unitDisc) = H ⟨x, hxW⟩ := by
    apply Subtype.ext
    change G (i.symm x) = G ⟨x, hxW⟩
    rw [hei]
  rw [heval]
  exact congrFun hH ⟨x, hxW⟩

end SurfaceDynamics.BKL

end

section

/-! # Source containment for surface fillings over a regular punctured disc -/

open Set Function Metric Topology
open scoped Manifold
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

theorem compactFill_subset_denseCompletion_of_regular_puncturedDisc
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (q : DiscCovering X)
    {t : unitDisc → X} (ht : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) t) (hte : IsOpenEmbedding t)
    (hreg : ∀ z : puncturedUnitDisc, t ⟨z, z.2.1⟩ ∈ f.regularValues)
    {K : Set X} (hK : IsCompact K) (hKc : IsConnected K) (hKs : K ⊆ f.source)
    (himage : MapsTo f.totalize K (range (fun w : puncturedUnitDisc => t ⟨w, w.2.1⟩)))
    (e : OpenPartialHomeomorph X ℂ) (hes : compactFill K ⊆ e.source)
    (het : e.target ⊆ unitDisc)
    (hproj : ∀ x (_hx : x ∈ e.source), ∀ heD : e x ∈ unitDisc,
      q.projection ⟨e x, heD⟩ = x) :
    compactFill K ⊆ f.denseCompletionSource := by
  let : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  have hKe : K ⊆ e.source := (subset_compactFill K).trans hes
  have hLe : e '' K ⊆ ball 0 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact het (e.map_source (hKe hx))
  have hLK : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKe)
  have hLc : IsConnected (e '' K) := hKc.image e (e.continuousOn.mono hKe)
  have hsource : ∀ z ∈ e '' K, ∀ hzd : z ∈ ball 0 1,
      q.projection ⟨z, hzd⟩ ∈ f.source := by
    rintro _ ⟨x, hx, rfl⟩ hzd
    rw [hproj x (hKe hx) hzd]
    exact hKs hx
  have him : ∀ z ∈ e '' K, ∀ hzd : z ∈ ball 0 1,
      f.totalize (q.projection ⟨z, hzd⟩) ∈
        range (fun w : puncturedUnitDisc => t ⟨w, w.2.1⟩) := by
    rintro _ ⟨x, hx, rfl⟩ hzd
    rw [hproj x (hKe hx) hzd]
    exact himage hx
  obtain ⟨_, hfill⟩ := projected_fill_subset_denseCompletion_of_regular_puncturedDisc
    f hf q ht hte hreg hLK hLc hLe hsource him
  have hchart := image_compactFill_subset_compactFill_image_local hK.isClosed hes
    e.continuousOn (fun S hS hSo => e.isOpen_image_of_subset_source hSo hS)
  rw [compactFill_complex_eq_fill] at hchart
  intro x hx
  have heD := het (e.map_source (hes hx))
  have hh := hfill (e x) (hchart (mem_image_of_mem e hx)) heD
  rwa [hproj x (hes hx) heD] at hh

theorem compactFill_subset_denseCompletion_in_simplyConnected_neighborhood
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (q : ComponentwiseDiscCover X)
    {t : unitDisc → X} (ht : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) t) (hte : IsOpenEmbedding t)
    (hreg : ∀ z : puncturedUnitDisc, t ⟨z, z.2.1⟩ ∈ f.regularValues)
    {K : Set X} (hK : IsCompact K) (hKc : IsConnected K) (hKs : K ⊆ f.source)
    (himage : MapsTo f.totalize K (range (fun w : puncturedUnitDisc => t ⟨w, w.2.1⟩)))
    (W : TopologicalSpace.Opens X) [SimplyConnectedSpace W]
    (hKW : compactFill K ⊆ W) :
    compactFill K ⊆ f.denseCompletionSource := by
  obtain ⟨x, hx⟩ := hKc.nonempty
  let x₀ : W := ⟨x, hKW (subset_compactFill K hx)⟩
  let q₀ := q.discCovering (ConnectedComponents.mk x)
  obtain ⟨e, hes, het, _, hproj⟩ := exists_cover_inverse_chart q₀ W x₀
    (q.mem_discCovering_range x)
  apply compactFill_subset_denseCompletion_of_regular_puncturedDisc
    f hf q₀ ht hte hreg hK hKc hKs himage e _ het hproj
  rwa [hes]

end SurfaceDynamics.BKL

end

section

/-! # Eventual source containment of the filled wandering covering discs -/

open Set Function Filter Metric Topology
open scoped Manifold
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

theorem disjoint_disc_fillings_eventually_subset_denseCompletion
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [NoncompactComponents X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (q : ComponentwiseDiscCover X)
    {K : Set X} (hK : IsCompact K) (hKd : Disjoint K (derivedSet f.singularValues))
    (F : ℕ → unitDisc → X) (hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n))
    (hcentre : ∀ n, F n discZero ∈ K)
    (hdis : Pairwise (fun n m => Disjoint (range (F n)) (range (F m))))
    (hsource : ∀ n, range (F n) ⊆ f.source)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hnext : ∀ n, MapsTo f.totalize (F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r})
      (F (n + 1) '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r})) :
    ∀ᶠ n in atTop,
      compactFill (F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r}) ⊆ f.denseCompletionSource := by
  have ht := (tendsto_add_atTop_nat 1).eventually
    (disjoint_discs_eventually_in_regular_punctured_coordDisk f q hK hKd F hF hcentre hdis hr1)
  have hs := disjoint_disc_fillings_eventually_in_simplyConnected_neighborhood
    q hK F hF hcentre hdis hr1
  filter_upwards [ht, hs] with n hn hns
  obtain ⟨D, hreg, hD⟩ := hn
  obtain ⟨W, hW, hCW⟩ := hns
  let : SimplyConnectedSpace W := hW
  apply compactFill_subset_denseCompletion_in_simplyConnected_neighborhood f hf q
    D.mdifferentiable_param D.isOpenEmbedding_param hreg
    ((unitDisc_closed_radius_compact hr1).image (hF n).continuous)
    ((unitDisc_closed_radius_connected hr hr1).image _ (hF n).continuous.continuousOn)
    (fun _ hx => hsource n (image_subset_range _ _ hx))
    (fun _ hx => hD (hnext n hx)) W hCW

end SurfaceDynamics.BKL

end

section

/-! # Only finitely many singular values meet the late filled discs -/

open Set Function Filter Metric Topology
open scoped Manifold
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

theorem disjoint_disc_fillings_eventually_finite_singular_intersection
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] [NoncompactComponents X]
    (f : LocalMap X) (q : ComponentwiseDiscCover X) {K : Set X} (hK : IsCompact K)
    (hKd : Disjoint K (derivedSet f.singularValues))
    (F : ℕ → unitDisc → X) (hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n))
    (hcentre : ∀ n, F n discZero ∈ K)
    (hdis : Pairwise (fun n m => Disjoint (range (F n)) (range (F m)))) :
    ∃ E : Set X, E.Finite ∧ ∀ r : ℝ, r < 1 → ∀ᶠ n in atTop,
      compactFill (F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r}) ∩ f.singularValues ⊆ E := by
  classical
  have hlocal : ∀ x : K, ∃ D : RiemannDynamics.CoordDisk X,
      D.center = (x : X) ∧ ∀ y ∈ D.closedCarrier, y ∈ f.singularValues → y = D.center := by
    intro x
    have he := eventually_eq_of_mem_of_not_accPt (disjoint_left.mp hKd x.2)
    obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.mp he
    obtain ⟨D, hD, hDW⟩ := exists_coordDisk_center_closedCarrier_subset hWo hxW
    exact ⟨D, hD, fun y hy hys => (hW (hDW hy) hys).trans hD.symm⟩
  choose D hD hsing using hlocal
  have hcover : K ⊆ ⋃ x : K, range (D x).param := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, discZero, (D ⟨x, hx⟩).param_zero.trans (hD ⟨x, hx⟩)⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover (fun x : K => range (D x).param)
    (fun x => (D x).isOpenEmbedding_param.isOpen_range) hcover
  have hcoverI : K ⊆ ⋃ x : ↥I, range (D x).param := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := mem_iUnion₂.mp (hI hx)
    exact mem_iUnion.mpr ⟨⟨a, ha⟩, hax⟩
  refine ⟨range (fun x : ↥I => (D x).center), Set.finite_range _, ?_⟩
  intro r hr
  have hh := q.disjoint_disc_images_eventually_in_cover hK F hF hcentre hdis
    (fun x : ↥I => range (D x).param)
    (fun x => (D x).isOpenEmbedding_param.isOpen_range) hcoverI hr
  filter_upwards [hh] with n hn
  obtain ⟨a, ha⟩ := hn
  have hC : F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r} ⊆ (D a).closedCarrier := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨w, hw⟩ := ha z hz
    exact hw ▸ (D a).param_mem_closedCarrier w
  intro x hx
  exact ⟨a, (hsing a x (compactFill_subset_coordDisk_of_noncompactComponents (D a) hC hx.1) hx.2).symm⟩

end SurfaceDynamics.BKL

end
