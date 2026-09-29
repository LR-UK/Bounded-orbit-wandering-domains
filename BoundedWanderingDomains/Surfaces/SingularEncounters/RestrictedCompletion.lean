module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.BKL.AnalyticCompletion
public import BoundedWanderingDomains.Surfaces.LocalMapRestriction

@[expose] public section

/-! # Analytic completion commutes with restriction on the common domain

An extension of a source restriction is an extension of the original map on
the same open set: density and continuity force agreement there. In particular,
filling a removable puncture of an inverse component gives a legitimate local
extension of the original map.
-/

open Set Function Filter Topology
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- Regard a dense extension of a source restriction as an extension of the
original map, without changing its domain or its values. -/
noncomputable def DenseExtension.of_restrictSource
    {f : LocalMap X} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map)
    {V : TopologicalSpace.Opens X} {hV : (V : Set X) ⊆ f.source}
    (d : DenseExtension (f.restrictSource V hV)) : DenseExtension f where
  source := d.source
  value := d.value
  holomorphic := d.holomorphic
  dense := d.dense.trans (closure_mono hV)
  agrees := by
    intro x hx ho
    let e := DenseExtension.original f hf
    have hd : (d.source : Set X) ∩ f.source ⊆
        closure (((d.source : Set X) ∩ f.source) ∩ (V : Set X)) := by
      intro y hy
      rw [mem_closure_iff]
      intro W hW hyW
      obtain ⟨z, hzW, hzV⟩ := mem_closure_iff.mp (d.dense hy.1)
        (W ∩ ((d.source : Set X) ∩ f.source))
        (hW.inter (d.source.isOpen.inter f.source.isOpen)) ⟨hyW, hy⟩
      exact ⟨z, hzW.1, hzW.2, hzV⟩
    have heq : EqOn d.value e.value
        (((d.source : Set X) ∩ f.source) ∩ (V : Set X)) := by
      intro y hy
      exact (d.agrees y hy.1.1 hy.2).trans (e.agrees y hy.1.2 hy.1.2).symm
    have hcomp : EqOn d.value e.value ((d.source : Set X) ∩ f.source) :=
      heq.of_subset_closure
        (d.holomorphic.continuousOn.mono inter_subset_left)
        (e.holomorphic.continuousOn.mono inter_subset_right) inter_subset_left hd
    exact (hcomp ⟨hx, ho⟩).trans (e.agrees x ho ho)

theorem denseCompletionSource_restrictSource_subset
    (f : LocalMap X) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map)
    (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source) :
    ((f.restrictSource V hV).denseCompletionSource : Set X) ⊆ f.denseCompletionSource := by
  rintro x ⟨d, hx⟩
  exact ⟨d.of_restrictSource hf, hx⟩

theorem denseCompletionValue_restrictSource_eq
    (f : LocalMap X) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map)
    (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source)
    {x : X} (hx : x ∈ (f.restrictSource V hV).denseCompletionSource) :
    (f.restrictSource V hV).denseCompletionValue x = f.denseCompletionValue x := by
  obtain ⟨d, hd⟩ := hx
  rw [(f.restrictSource V hV).denseCompletionValue_eq d hd,
    f.denseCompletionValue_eq (d.of_restrictSource hf) hd]
  rfl

/-- An added point detected in a restricted completion maps to an exceptional
value of that restriction. Other inverse components play no role. -/
theorem denseCompletionValue_mem_of_restricted_added
    [IsManifold 𝓘(ℂ) 1 X] [LocallyCompactSpace X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source)
    {D E : Set X} (hS : (f.restrictSource V hV).singularValues ∩ D ⊆ E)
    {x : X} (hx : x ∈ (f.restrictSource V hV).denseCompletionSource)
    (hxo : x ∉ f.source) (himage : f.denseCompletionValue x ∈ D) :
    f.denseCompletionValue x ∈ E := by
  have hs := (f.restrictSource V hV).added_image_mem_singularValues
    (f.isOpenHolomorphic_restrictSource hf V hV) ⟨x, hx⟩ (fun h => hxo (hV h))
  change (f.restrictSource V hV).denseCompletionValue x ∈
    (f.restrictSource V hV).singularValues at hs
  rw [f.denseCompletionValue_restrictSource_eq hf.2 V hV hx] at hs
  exact hS ⟨hs, himage⟩

end SurfaceDynamics.LocalMap
