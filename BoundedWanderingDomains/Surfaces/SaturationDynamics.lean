/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.LocalMapTotalization
import BoundedWanderingDomains.Surfaces.Statements
import BoundedWanderingDomains.Surfaces.SurfacePolish

/-! # Measurable forward saturations for local surface dynamics -/

open Set Function
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X]

theorem subset_saturation (f : LocalMap X) (A : Set X) : A ⊆ f.saturation A := by
  intro x hx
  exact mem_iUnion.mpr ⟨0, by simpa [saturation] using hx⟩

theorem imageAt_subset_trapped (f : LocalMap X) {A : Set X}
    (hA : A ⊆ f.trapped) (n : ℕ) : f.imageAt n A ⊆ f.trapped := by
  rintro y ⟨x, hx, hxy⟩
  let xt : f.trapped := ⟨x, hA hx⟩
  have he := f.iterate_eq_some_orbit n xt
  have hy : y = f.orbit n xt := Option.some.inj (hxy.symm.trans he)
  rw [hy]
  exact ((f.trappedMap^[n]) xt).property

theorem saturation_subset_trapped (f : LocalMap X) {A : Set X}
    (hA : A ⊆ f.trapped) : f.saturation A ⊆ f.trapped := by
  rintro x hx
  obtain ⟨n, hn⟩ := mem_iUnion.mp hx
  exact f.imageAt_subset_trapped hA n hn

/-- On a trapped starting set, one application of the harmless totalisation
sends the `n`th partial image exactly to the `(n+1)`st partial image. -/
theorem totalize_image_imageAt (f : LocalMap X) {A : Set X}
    (hA : A ⊆ f.trapped) (n : ℕ) :
    f.totalize '' f.imageAt n A = f.imageAt (n + 1) A := by
  ext y
  constructor
  · rintro ⟨w, ⟨x, hx, hxw⟩, rfl⟩
    let xt : f.trapped := ⟨x, hA hx⟩
    have hw : w = f.orbit n xt :=
      Option.some.inj (hxw.symm.trans (f.iterate_eq_some_orbit n xt))
    refine ⟨x, hx, ?_⟩
    rw [f.iterate_eq_some_orbit (n + 1) xt]
    congr 1
    rw [hw, f.orbit_succ, f.totalize_eq (f.orbit_mem_source n xt)]
  · rintro ⟨x, hx, hxy⟩
    let xt : f.trapped := ⟨x, hA hx⟩
    let w := f.orbit n xt
    have hw : w ∈ f.imageAt n A :=
      ⟨x, hx, f.iterate_eq_some_orbit n xt⟩
    refine ⟨w, hw, ?_⟩
    have hy : y = f.orbit (n + 1) xt :=
      Option.some.inj (hxy.symm.trans (f.iterate_eq_some_orbit (n + 1) xt))
    dsimp only [w]
    rw [hy, f.orbit_succ, f.totalize_eq (f.orbit_mem_source n xt)]

theorem totalize_injOn_saturation (f : LocalMap X) {A : Set X}
    (hA : A ⊆ f.trapped) (hinj : f.InjectiveOnSaturation A) :
    InjOn f.totalize (f.saturation A) := by
  intro x hx y hy he
  have hxs : x ∈ f.source :=
    f.trapped_subset_source (f.saturation_subset_trapped hA hx)
  have hys : y ∈ f.source :=
    f.trapped_subset_source (f.saturation_subset_trapped hA hy)
  have hmap : f.map ⟨x, hxs⟩ = f.map ⟨y, hys⟩ := by
    simpa only [f.totalize_eq hxs, f.totalize_eq hys] using he
  have hsub : (⟨x, hxs⟩ : f.source) = ⟨y, hys⟩ := hinj hx hy hmap
  exact congrArg Subtype.val hsub

theorem totalize_image_saturation (f : LocalMap X) {A : Set X}
    (hA : A ⊆ f.trapped)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A))) :
    f.totalize '' f.saturation A = f.saturation A \ A := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp hw
    have hnext : f.totalize w ∈ f.imageAt (n + 1) A := by
      rw [← f.totalize_image_imageAt hA n]
      exact ⟨w, hn, rfl⟩
    refine ⟨mem_iUnion.mpr ⟨n + 1, hnext⟩, ?_⟩
    intro hzero
    have hzero' : f.totalize w ∈ f.imageAt 0 A := by simpa using hzero
    exact Set.disjoint_left.mp (hdis (by omega : n + 1 ≠ 0)) hnext hzero'
  · rintro ⟨hy, hyA⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp hy
    cases n with
    | zero => exact False.elim (hyA (by simpa using hn))
    | succ n =>
        rw [← f.totalize_image_imageAt hA n] at hn
        obtain ⟨w, hw, rfl⟩ := hn
        exact ⟨w, mem_iUnion.mpr ⟨n, hw⟩, rfl⟩

section Measurable

variable [MeasurableSpace X] [BorelSpace X] [T2Space X]
  [SecondCountableTopology X] [LocallyCompactSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

theorem measurableSet_imageAt (f : LocalMap X) {A : Set X}
    (hf : Continuous f.map) (hA : A ⊆ f.trapped)
    (hinj : f.InjectiveOnSaturation A) (hm : MeasurableSet A) (n : ℕ) :
    MeasurableSet (f.imageAt n A) := by
  letI : PolishSpace X := AreaDeficit.Surfaces.surfacePolishSpace
  induction n with
  | zero => simpa using hm
  | succ n ih =>
      rw [← f.totalize_image_imageAt hA n]
      apply ih.image_of_continuousOn_injOn
      · exact (f.continuousOn_totalize hf).mono
          (f.imageAt_subset_source hA n)
      · exact (f.totalize_injOn_saturation hA hinj).mono
          (fun _ hx => mem_iUnion.mpr ⟨n, hx⟩)

theorem measurableSet_saturation (f : LocalMap X) {A : Set X}
    (hf : Continuous f.map) (hA : A ⊆ f.trapped)
    (hinj : f.InjectiveOnSaturation A) (hm : MeasurableSet A) :
    MeasurableSet (f.saturation A) := by
  letI : PolishSpace X := AreaDeficit.Surfaces.surfacePolishSpace
  exact MeasurableSet.iUnion (f.measurableSet_imageAt hf hA hinj hm)

end Measurable

end SurfaceDynamics.LocalMap
