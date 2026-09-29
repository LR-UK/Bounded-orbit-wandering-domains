module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.OmegaDynamics
public import BoundedWanderingDomains.Surfaces.SaturationDynamics

@[expose] public section

/-! # Injective iterates and shifts of wandering sets -/

open Set Function Filter Topology
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X]

theorem imageAt_eq_totalize_iterate_image (f : LocalMap X) {A : Set X}
    (hA : A ⊆ f.trapped) (n : ℕ) :
    f.imageAt n A = (f.totalize^[n]) '' A := by
  ext y
  constructor
  · rintro ⟨x, hx, he⟩
    refine ⟨x, hx, ?_⟩
    rw [f.totalize_iterate_orbit n ⟨x, hA hx⟩]
    exact Option.some.inj ((f.iterate_eq_some_orbit n ⟨x, hA hx⟩).symm.trans he)
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [f.totalize_iterate_orbit n ⟨x, hA hx⟩]
    exact f.iterate_eq_some_orbit n ⟨x, hA hx⟩

theorem imageAt_imageAt (f : LocalMap X) {A : Set X}
    (hA : A ⊆ f.trapped) (n m : ℕ) :
    f.imageAt n (f.imageAt m A) = f.imageAt (n + m) A := by
  rw [f.imageAt_eq_totalize_iterate_image (f.imageAt_subset_trapped hA m),
    f.imageAt_eq_totalize_iterate_image hA m, f.imageAt_eq_totalize_iterate_image hA]
  rw [← image_comp, ← Function.iterate_add]

theorem saturation_imageAt_subset (f : LocalMap X) {A : Set X}
    (hA : A ⊆ f.trapped) (N : ℕ) :
    f.saturation (f.imageAt N A) ⊆ f.saturation A := by
  intro x hx
  obtain ⟨n, hn⟩ := mem_iUnion.mp hx
  rw [f.imageAt_imageAt hA] at hn
  exact mem_iUnion.mpr ⟨n + N, hn⟩

theorem pairwise_disjoint_imageAt_shift (f : LocalMap X) {A : Set X}
    (hA : A ⊆ f.trapped)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (N : ℕ) : Pairwise (fun n m : ℕ =>
      Disjoint (f.imageAt n (f.imageAt N A)) (f.imageAt m (f.imageAt N A))) := by
  intro n m hnm
  rw [f.imageAt_imageAt hA, f.imageAt_imageAt hA]
  exact hdis (by omega)

theorem injectiveOnSaturation_of_iterates_injective (f : LocalMap X) {A : Set X}
    (hA : A ⊆ f.trapped)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : ∀ n, InjOn (f.compactifiedIterate n) A) : f.InjectiveOnSaturation A := by
  intro x hx y hy he
  obtain ⟨n, a, ha, hax⟩ := mem_iUnion.mp hx
  obtain ⟨m, b, hb, hby⟩ := mem_iUnion.mp hy
  have hxnext : f.map x ∈ f.imageAt (n + 1) A := by
    rw [← f.totalize_image_imageAt hA n]
    exact ⟨x, ⟨a, ha, hax⟩, f.totalize_eq x.property⟩
  have hynext : f.map x ∈ f.imageAt (m + 1) A := by
    rw [he, ← f.totalize_image_imageAt hA m]
    exact ⟨y, ⟨b, hb, hby⟩, f.totalize_eq y.property⟩
  have hnm : n = m := by
    by_contra hh
    exact disjoint_left.mp (hdis (by omega : n + 1 ≠ m + 1)) hxnext hynext
  subst m
  have hax' : (f.totalize^[n]) a = (x : X) := by
    rw [f.totalize_iterate_orbit n ⟨a, hA ha⟩]
    exact Option.some.inj ((f.iterate_eq_some_orbit n ⟨a, hA ha⟩).symm.trans hax)
  have hby' : (f.totalize^[n]) b = (y : X) := by
    rw [f.totalize_iterate_orbit n ⟨b, hA hb⟩]
    exact Option.some.inj ((f.iterate_eq_some_orbit n ⟨b, hA hb⟩).symm.trans hby)
  have hab : a = b := hinj (n + 1) ha hb (by
    rw [f.compactifiedIterate_eq_orbit (n + 1) ⟨a, hA ha⟩,
      f.compactifiedIterate_eq_orbit (n + 1) ⟨b, hA hb⟩,
      ← f.totalize_iterate_orbit, ← f.totalize_iterate_orbit,
      Function.iterate_succ_apply', Function.iterate_succ_apply', hax', hby',
      f.totalize_eq x.property, f.totalize_eq y.property, he])
  exact Subtype.ext (hax'.symm.trans (hab ▸ hby'))

variable [T2Space X] [LocallyCompactSpace X]

theorem mem_omega_of_totalize_mem (f : LocalMap X) (hf : Continuous f.map)
    {x : X} (hxs : x ∈ f.source) (hfx : f.totalize x ∈ f.omega) : x ∈ f.omega := by
  obtain ⟨V, hVo, hfxV, hVtr, hVN⟩ := hfx
  let W : Set X := f.source ∩ f.totalize ⁻¹' V
  have hWo : IsOpen W := (f.continuousOn_totalize hf).isOpen_inter_preimage f.source.isOpen hVo
  have hWtr : W ⊆ f.trapped := by
    intro y hy n
    cases n with
    | zero => exact ⟨y, hy.1, rfl⟩
    | succ n =>
        obtain ⟨z, hz, he⟩ := hVtr hy.2 n
        exact ⟨z, hz, by rwa [f.iterate_succ n y hy.1, ← f.totalize_eq hy.1]⟩
  refine ⟨W, hWo, ⟨hxs, hfxV⟩, hWtr, ?_⟩
  intro φ hφ
  let : UniformSpace (OnePoint X) := uniformSpaceOfCompactR1
  let θ : ℕ → ℕ := fun n => φ (n + 1) - 1
  have hθ : StrictMono θ := by
    intro n m hnm
    have hpos := hφ (show 0 < n + 1 by omega)
    have hlt := hφ (Nat.add_lt_add_right hnm 1)
    dsimp [θ]
    omega
  obtain ⟨ψ, hψ, G, hG⟩ := hVN θ hθ
  let g : W → V := fun y => ⟨f.totalize y, y.property.2⟩
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    exact (f.continuousOn_totalize hf).comp_continuous continuous_subtype_val
      (fun y => y.property.1)
  refine ⟨fun n => ψ n + 1, fun n m hnm => Nat.add_lt_add_right (hψ hnm) 1, G ∘ g, ?_⟩
  apply (hG.comp g hg).congr
  intro n y
  have hpos := hφ (show 0 < ψ n + 1 by omega)
  have he : φ (ψ n + 1) = θ (ψ n) + 1 := by dsimp [θ]; omega
  rw [he]
  unfold compactifiedIterate
  rw [f.iterate_succ _ y y.property.1, ← f.totalize_eq y.property.1]
  rfl

theorem imageAt_subset_trapped_diff_omega (f : LocalMap X) (hf : Continuous f.map)
    {A : Set X} (hA : A ⊆ f.trapped \ f.omega) (n : ℕ) :
    f.imageAt n A ⊆ f.trapped \ f.omega := by
  induction n with
  | zero => simpa using hA
  | succ n ih =>
      rw [← f.totalize_image_imageAt (fun x hx => (hA hx).1) n]
      rintro y ⟨x, hx, rfl⟩
      have hxt := (ih hx).1
      refine ⟨?_, fun h => (ih hx).2 (f.mem_omega_of_totalize_mem hf
        (f.trapped_subset_source hxt) h)⟩
      rw [f.totalize_eq (f.trapped_subset_source hxt)]
      exact f.trapped_forward hxt

end SurfaceDynamics.LocalMap
