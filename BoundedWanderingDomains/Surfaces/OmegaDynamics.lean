/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.LocalCoveringDiscs
import BoundedWanderingDomains.Surfaces.WanderingOrbitStructure

/-! # Forward invariance of the genuine normality components -/

open Set Function Filter Topology
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]

theorem totalize_mapsTo_omega (f : LocalMap X) (hf : IsOpenHolomorphic f) :
    MapsTo f.totalize f.omega f.omega := by
  classical
  rintro x ⟨W, hWo, hxW, hWT, hWN⟩
  obtain ⟨C, hCc, hxC, hCW⟩ := exists_compact_subset hWo hxW
  let T := f.totalize '' interior C
  have hICsource : interior C ⊆ f.source :=
    interior_subset.trans (hCW.trans (hWT.trans f.trapped_subset_source))
  have hTo : IsOpen T := f.isOpen_image_totalize hf.1 isOpen_interior hICsource
  have hTT : T ⊆ f.trapped := by
    rintro y ⟨w, hw, rfl⟩
    rw [f.totalize_eq (hICsource hw)]
    exact f.trapped_forward (hWT (hCW (interior_subset hw)))
  refine ⟨T, hTo, ⟨x, hxC, rfl⟩, hTT, ?_⟩
  intro φ hφ
  let : UniformSpace (OnePoint X) := uniformSpaceOfCompactR1
  obtain ⟨ψ, hψ, G, hG⟩ := hWN (fun n => φ n + 1) (by
    intro n m hnm
    exact Nat.add_lt_add_right (hφ hnm) 1)
  have hpre : ∀ y : T, ∃ w : W, (w : X) ∈ C ∧ f.totalize w = (y : X) := by
    intro y
    obtain ⟨w, hw, he⟩ := y.property
    exact ⟨⟨w, hCW (interior_subset hw)⟩, interior_subset hw, he⟩
  choose s hsC hs using hpre
  let CW : Set W := Subtype.val ⁻¹' C
  have hCWc : IsCompact CW := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, image_preimage_eq_inter_range]
    convert hCc using 1
    exact inter_eq_left.mpr (fun y hy => ⟨⟨y, hCW hy⟩, rfl⟩)
  have huni := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hCWc).mp
    hG.tendstoLocallyUniformlyOn
  have hcomp : TendstoUniformly
      (fun n y => f.compactifiedIterate (φ (ψ n) + 1) (s y)) (G ∘ s) atTop := by
    intro u hu
    filter_upwards [huni u hu] with n hn
    intro y
    exact hn (s y) (hsC y)
  refine ⟨ψ, hψ, G ∘ s, ?_⟩
  apply hcomp.tendstoLocallyUniformly.congr
  intro n y
  unfold compactifiedIterate
  rw [f.iterate_succ (φ (ψ n)) (s y) (f.trapped_subset_source (hWT (s y).property)),
    ← f.totalize_eq (f.trapped_subset_source (hWT (s y).property)), hs y]

theorem mapsTo_component_of_imageAt (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {S : ℕ → Set X} {U : Set X} (hS : ∀ n, f.IsComponent (S n))
    (himage : ∀ n, f.imageAt n U ⊆ S n) {z : X} (hz : z ∈ U)
    (hztrap : z ∈ f.trapped) : ∀ n, MapsTo f.totalize (S n) (S (n + 1)) := by
  intro n
  obtain ⟨a, ha, hSa⟩ := hS n
  obtain ⟨b, hb, hSb⟩ := hS (n + 1)
  have hSomega : S n ⊆ f.omega := hSa ▸ connectedComponentIn_subset _ _
  have hSc : IsPreconnected (S n) := by
    rw [hSa]
    exact isPreconnected_connectedComponentIn
  have hc : IsPreconnected (f.totalize '' S n) := by
    apply hSc.image
    exact (f.continuousOn_totalize hf.2.continuous).mono
      (hSomega.trans f.omega_subset_source)
  let zn := f.orbit n ⟨z, hztrap⟩
  have hzn : zn ∈ S n := himage n ⟨z, hz, f.iterate_eq_some_orbit n ⟨z, hztrap⟩⟩
  have hznext : f.totalize zn ∈ S (n + 1) := by
    rw [f.totalize_eq (f.orbit_mem_source n ⟨z, hztrap⟩), ← f.orbit_succ]
    exact himage (n + 1) ⟨z, hz, f.iterate_eq_some_orbit (n + 1) ⟨z, hztrap⟩⟩
  have hsub : f.totalize '' S n ⊆ f.omega := by
    rintro y ⟨x, hx, rfl⟩
    exact f.totalize_mapsTo_omega hf (hSomega hx)
  apply mapsTo_iff_image_subset.mpr
  calc
    f.totalize '' S n ⊆ connectedComponentIn f.omega (f.totalize zn) :=
      hc.subset_connectedComponentIn ⟨zn, hzn, rfl⟩ hsub
    _ = S (n + 1) := (connectedComponentIn_eq (hSb ▸ hznext)).symm.trans hSb.symm

end SurfaceDynamics.LocalMap
