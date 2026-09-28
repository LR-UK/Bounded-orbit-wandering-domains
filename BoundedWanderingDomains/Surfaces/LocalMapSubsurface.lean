/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.LocalDynamics
import BoundedWanderingDomains.Surfaces.PlaneReading
import BoundedWanderingDomains.Surfaces.RestrictedOmega
import BoundedWanderingDomains.Surfaces.Statements
import BoundedWanderingDomains.Surfaces.SubtypeHolomorphic

/-! # Reading a local map inside an invariant open subsurface -/

open Set Function
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X]

/-- A local map whose source and image lie in an open subsurface, read as a
local self-map of that subsurface. -/
def restrictAmbient (f : LocalMap X) (O : TopologicalSpace.Opens X)
    (_hsource : (f.source : Set X) ⊆ O)
    (hmap : ∀ x : f.source, f.map x ∈ O) : LocalMap O where
  source := ⟨{x : O | (x : X) ∈ f.source},
    f.source.isOpen.preimage continuous_subtype_val⟩
  map := fun x =>
    ⟨f.map ⟨((x : (O : Set X)) : X), x.property⟩,
      hmap ⟨((x : (O : Set X)) : X), x.property⟩⟩

@[simp] theorem restrictAmbient_source_coe (f : LocalMap X)
    (O : TopologicalSpace.Opens X) (hsource : (f.source : Set X) ⊆ O)
    (hmap : ∀ x : f.source, f.map x ∈ O) :
    ((f.restrictAmbient O hsource hmap).source : Set O) =
      {x : O | (x : X) ∈ f.source} := rfl

/-- The source of the subsurface reading is canonically homeomorphic to the
original source. -/
def restrictAmbientSourceHomeomorph (f : LocalMap X)
    (O : TopologicalSpace.Opens X) (hsource : (f.source : Set X) ⊆ O)
    (hmap : ∀ x : f.source, f.map x ∈ O) :
    (f.restrictAmbient O hsource hmap).source ≃ₜ f.source where
  toFun x := ⟨((x : O) : X), x.property⟩
  invFun x := ⟨⟨(x : X), hsource x.property⟩, x.property⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val

@[simp] theorem restrictAmbient_map_val (f : LocalMap X)
    (O : TopologicalSpace.Opens X) (hsource : (f.source : Set X) ⊆ O)
    (hmap : ∀ x : f.source, f.map x ∈ O)
    (x : (f.restrictAmbient O hsource hmap).source) :
    (((f.restrictAmbient O hsource hmap).map x : O) : X) =
      f.map ((f.restrictAmbientSourceHomeomorph O hsource hmap) x) := by
  rfl

/-- Openness and holomorphicity are unchanged when both source and target
are read in an invariant open subsurface. -/
theorem isOpenHolomorphic_restrictAmbient [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X)
    (hf : IsOpenHolomorphic f) (O : TopologicalSpace.Opens X)
    (hsource : (f.source : Set X) ⊆ O)
    (hmap : ∀ x : f.source, f.map x ∈ O) :
    IsOpenHolomorphic (f.restrictAmbient O hsource hmap) := by
  let e := f.restrictAmbientSourceHomeomorph O hsource hmap
  have hediff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e := by
    apply (AreaDeficit.Surfaces.mdifferentiable_subtypeVal_comp_iff
      f.source e).mp
    exact (AreaDeficit.Surfaces.mdifferentiable_subtype_val O).comp
      (AreaDeficit.Surfaces.mdifferentiable_subtype_val
        (f.restrictAmbient O hsource hmap).source)
  have hopenX : IsOpenMap (f.map ∘ e) := hf.1.comp e.isOpenMap
  have hopenO : IsOpenMap (fun x =>
      ⟨f.map (e x), hmap (e x)⟩ :
        (f.restrictAmbient O hsource hmap).source → O) :=
    hopenX.subtype_mk (fun x => hmap (e x))
  have hdiffX : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f.map ∘ e) := by
    exact hf.2.comp hediff
  have hdiffO : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x =>
      ⟨f.map (e x), hmap (e x)⟩ :
        (f.restrictAmbient O hsource hmap).source → O) := by
    apply (AreaDeficit.Surfaces.mdifferentiable_subtypeVal_comp_iff O _).mp
    exact hdiffX
  change IsOpenMap (fun x =>
      ⟨f.map (e x), hmap (e x)⟩ :
        (f.restrictAmbient O hsource hmap).source → O) ∧
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x =>
      ⟨f.map (e x), hmap (e x)⟩ :
        (f.restrictAmbient O hsource hmap).source → O)
  exact ⟨hopenO, hdiffO⟩

/-- Partial iteration commutes with the inclusion of the invariant open
subsurface into the original surface. -/
theorem restrictAmbient_iterate_val (f : LocalMap X)
    (O : TopologicalSpace.Opens X) (hsource : (f.source : Set X) ⊆ O)
    (hmap : ∀ x : f.source, f.map x ∈ O) (n : ℕ) (x : O) :
    Option.map ((↑) : O → X)
        ((f.restrictAmbient O hsource hmap).iterate n x) =
      f.iterate n (x : X) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      by_cases hx : (x : X) ∈ f.source
      · rw [(f.restrictAmbient O hsource hmap).iterate_succ n x hx,
          f.iterate_succ n (x : X) hx]
        change Option.map ((↑) : O → X)
            ((f.restrictAmbient O hsource hmap).iterate n
              ⟨f.map ⟨(x : X), hx⟩, hmap ⟨(x : X), hx⟩⟩) =
          f.iterate n (f.map ⟨(x : X), hx⟩)
        exact ih ⟨f.map ⟨(x : X), hx⟩, hmap ⟨(x : X), hx⟩⟩
      · simp [LocalMap.iterate, LocalMap.step, restrictAmbient, hx]

/-- Trappedness is unchanged by reading an invariant local map inside the
open subsurface. -/
theorem mem_restrictAmbient_trapped_iff (f : LocalMap X)
    (O : TopologicalSpace.Opens X) (hsource : (f.source : Set X) ⊆ O)
    (hmap : ∀ x : f.source, f.map x ∈ O) (x : O) :
    x ∈ (f.restrictAmbient O hsource hmap).trapped ↔
      (x : X) ∈ f.trapped := by
  constructor
  · intro hx n
    obtain ⟨y, hy, hxy⟩ := hx n
    refine ⟨(y : O), hy, ?_⟩
    have hm := congrArg (Option.map ((↑) : O → X)) hxy
    simpa only [f.restrictAmbient_iterate_val O hsource hmap,
      Option.map_some] using hm
  · intro hx n
    obtain ⟨y, hy, hxy⟩ := hx n
    let yo : O := ⟨y, hsource hy⟩
    have hm := f.restrictAmbient_iterate_val O hsource hmap n x
    rw [hxy] at hm
    cases he : (f.restrictAmbient O hsource hmap).iterate n x with
    | none => simp [he] at hm
    | some z =>
        have hzy : (z : X) = y := by
          rw [he] at hm
          exact Option.some.inj hm
        have hzyo : z = yo := Subtype.ext hzy
        refine ⟨yo, ?_, ?_⟩
        · exact hy
        · simp [hzyo]

/-- Finite images commute with inclusion of the invariant subsurface. -/
theorem image_restrictAmbient_imageAt (f : LocalMap X)
    (O : TopologicalSpace.Opens X) (hsource : (f.source : Set X) ⊆ O)
    (hmap : ∀ x : f.source, f.map x ∈ O) (n : ℕ) (A : Set O) :
    ((↑) : O → X) '' (f.restrictAmbient O hsource hmap).imageAt n A =
      f.imageAt n (((↑) : O → X) '' A) := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hxA, hxz⟩, rfl⟩
    refine ⟨(x : X), ⟨x, hxA, rfl⟩, ?_⟩
    have hm := congrArg (Option.map ((↑) : O → X)) hxz
    simpa only [f.restrictAmbient_iterate_val O hsource hmap,
      Option.map_some] using hm
  · rintro ⟨x, ⟨w, hwA, rfl⟩, hxy⟩
    have hm := f.restrictAmbient_iterate_val O hsource hmap n w
    rw [hxy] at hm
    cases he : (f.restrictAmbient O hsource hmap).iterate n w with
    | none => simp [he] at hm
    | some z =>
        rw [he] at hm
        have hzy : (z : X) = y := Option.some.inj hm
        refine ⟨z, ⟨w, hwA, he⟩, hzy⟩

/-- Forward saturations commute with inclusion of the invariant
subsurface. -/
theorem image_restrictAmbient_saturation (f : LocalMap X)
    (O : TopologicalSpace.Opens X) (hsource : (f.source : Set X) ⊆ O)
    (hmap : ∀ x : f.source, f.map x ∈ O) (A : Set O) :
    ((↑) : O → X) '' (f.restrictAmbient O hsource hmap).saturation A =
      f.saturation (((↑) : O → X) '' A) := by
  rw [saturation, saturation, image_iUnion]
  congr 1
  funext n
  exact f.image_restrictAmbient_imageAt O hsource hmap n A

/-- Pairwise disjoint partial images pass to the invariant subsurface. -/
theorem pairwise_disjoint_imageAt_restrictAmbient (f : LocalMap X)
    (O : TopologicalSpace.Opens X) (hsource : (f.source : Set X) ⊆ O)
    (hmap : ∀ x : f.source, f.map x ∈ O) (A : Set O)
    (hdis : Pairwise (fun n m : ℕ =>
      Disjoint (f.imageAt n (((↑) : O → X) '' A))
        (f.imageAt m (((↑) : O → X) '' A)))) :
    Pairwise (fun n m : ℕ =>
      Disjoint ((f.restrictAmbient O hsource hmap).imageAt n A)
        ((f.restrictAmbient O hsource hmap).imageAt m A)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro z hzn hzm
  apply Set.disjoint_left.mp (hdis hnm)
  · rw [← f.image_restrictAmbient_imageAt O hsource hmap n A]
    exact ⟨z, hzn, rfl⟩
  · rw [← f.image_restrictAmbient_imageAt O hsource hmap m A]
    exact ⟨z, hzm, rfl⟩

/-- Injectivity on the forward saturation passes to the invariant
subsurface. -/
theorem injectiveOnSaturation_restrictAmbient (f : LocalMap X)
    (O : TopologicalSpace.Opens X) (hsource : (f.source : Set X) ⊆ O)
    (hmap : ∀ x : f.source, f.map x ∈ O) (A : Set O)
    (hinj : f.InjectiveOnSaturation (((↑) : O → X) '' A)) :
    (f.restrictAmbient O hsource hmap).InjectiveOnSaturation A := by
  intro x hx y hy hxy
  let e := f.restrictAmbientSourceHomeomorph O hsource hmap
  have hx' : (e x : X) ∈ f.saturation (((↑) : O → X) '' A) := by
    rw [← f.image_restrictAmbient_saturation O hsource hmap A]
    exact ⟨(x : O), hx, rfl⟩
  have hy' : (e y : X) ∈ f.saturation (((↑) : O → X) '' A) := by
    rw [← f.image_restrictAmbient_saturation O hsource hmap A]
    exact ⟨(y : O), hy, rfl⟩
  have hmapxy : f.map (e x) = f.map (e y) := by
    exact congrArg Subtype.val hxy
  have hexy : e x = e y := hinj hx' hy' hmapxy
  exact e.injective hexy

/-- For a relatively compact source inside the covered subsurface, a point
normal for the subsurface reading was already normal for the original local
map.  Compact-range Montel identifies both questions with interior
trappedness. -/
theorem omega_restrictAmbient_restrictSource_subset
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    [T2Space X] [LocallyCompactSpace X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (O V : TopologicalSpace.Opens X)
    [LocallyCompactSpace O]
    (p : AreaDeficit.Surfaces.DiscCover O)
    (hVsource : (V : Set X) ⊆ f.source)
    (hVcompact : IsCompact (closure (V : Set X)))
    (hVO : closure (V : Set X) ⊆ O)
    (hmap : ∀ x : (f.restrictSource V hVsource).source,
      (f.restrictSource V hVsource).map x ∈ O) :
    ((↑) : O → X) ''
        ((f.restrictSource V hVsource).restrictAmbient O
          (fun _ hx => hVO (subset_closure hx)) hmap).omega ⊆
      f.omega := by
  let r := f.restrictSource V hVsource
  let g := r.restrictAmbient O
    (fun _ hx => hVO (subset_closure hx)) hmap
  intro x hx
  obtain ⟨xo, hxo, rfl⟩ := hx
  have hxint : xo ∈ interior g.trapped :=
    g.omega_subset_trapped_interior hxo
  let W : Set X := ((↑) : O → X) '' interior g.trapped
  have hWopen : IsOpen W :=
    O.isOpen.isOpenMap_subtype_val _ isOpen_interior
  have hxW : (xo : X) ∈ W := ⟨xo, hxint, rfl⟩
  have hWr : W ⊆ r.trapped := by
    rintro _ ⟨y, hy, rfl⟩
    exact (r.mem_restrictAmbient_trapped_iff O
      (fun _ hz => hVO (subset_closure hz)) hmap y).mp
      (interior_subset hy)
  have hxri : (xo : X) ∈ interior r.trapped := by
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (hWopen.mem_nhds hxW) hWr
  have hxro : (xo : X) ∈ r.omega := by
    rw [f.omega_restrictSource_eq_interior_trapped hf O V p
      hVsource hVcompact hVO]
    exact hxri
  exact f.restrictSource_omega_subset V hVsource hxro

end SurfaceDynamics.LocalMap
