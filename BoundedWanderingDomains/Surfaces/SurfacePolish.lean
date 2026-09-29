module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import Mathlib.Geometry.Manifold.Metrizable
public import Mathlib.Geometry.Manifold.Complex
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Compactness.SigmaCompact

@[expose] public section

/-! # Polish presentations of second-countable locally compact surfaces -/

open Set TopologicalSpace
open scoped Manifold

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [SecondCountableTopology X] [LocallyCompactSpace X]

/-- The one-point compactification of a second-countable locally compact
Hausdorff space is second countable. -/
theorem onePointSecondCountableTopology :
    SecondCountableTopology (OnePoint X) := by
  let K : CompactExhaustion X := default
  let B : Set (Set (OnePoint X)) :=
    (fun s : Set X => ((↑) : X → OnePoint X) '' s) '' countableBasis X ∪
      range (fun n : ℕ => (((↑) : X → OnePoint X) '' K n)ᶜ)
  have hBc : B.Countable :=
    (countable_countableBasis (α := X)).image _ |>.union (Set.countable_range _)
  have hB : IsTopologicalBasis B := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · intro s hs
      rcases hs with hs | hs
      · obtain ⟨t, ht, rfl⟩ := hs
        exact OnePoint.isOpen_image_coe.mpr (isOpen_of_mem_countableBasis ht)
      · obtain ⟨n, rfl⟩ := hs
        exact OnePoint.isOpen_compl_image_coe.mpr
          ⟨(K.isCompact n).isClosed, K.isCompact n⟩
    · intro a u hau hu
      cases a with
      | infty =>
        have hcomp : IsCompact (((↑) : X → OnePoint X) ⁻¹' u)ᶜ :=
          (OnePoint.isOpen_iff_of_mem' hau).mp hu |>.1
        obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hcomp
        refine ⟨(((↑) : X → OnePoint X) '' K n)ᶜ,
          Or.inr ⟨n, rfl⟩, OnePoint.infty_notMem_image_coe, ?_⟩
        intro y hy
        cases y with
        | infty => exact hau
        | coe x =>
            have hxK : x ∉ K n := by
              intro hx
              exact hy ⟨x, hx, rfl⟩
            have hxpre : x ∈ ((↑) : X → OnePoint X) ⁻¹' u := by
              by_contra hx
              exact hxK (hn hx)
            exact hxpre
      | coe x =>
        have hxpre : x ∈ ((↑) : X → OnePoint X) ⁻¹' u := hau
        have hopen : IsOpen (((↑) : X → OnePoint X) ⁻¹' u) :=
          OnePoint.continuous_coe.isOpen_preimage _ hu
        obtain ⟨t, htB, hxt, htu⟩ :=
          (isBasis_countableBasis (α := X)).exists_subset_of_mem_open hxpre hopen
        refine ⟨((↑) : X → OnePoint X) '' t,
          Or.inl ⟨t, htB, rfl⟩, ⟨x, hxt, rfl⟩, ?_⟩
        rintro _ ⟨z, hzt, rfl⟩
        exact htu hzt
  exact hB.secondCountableTopology hBc

/-- A second-countable locally compact Hausdorff surface is Polish. -/
theorem surfacePolishSpace : PolishSpace X := by
  let : SecondCountableTopology (OnePoint X) := onePointSecondCountableTopology
  let : MetrizableSpace (OnePoint X) :=
    metrizableSpace_of_t3_secondCountable (OnePoint X)
  let : MetricSpace (OnePoint X) :=
    TopologicalSpace.metrizableSpaceMetric (OnePoint X)
  let : CompleteSpace (OnePoint X) := inferInstance
  let : PolishSpace (OnePoint X) := inferInstance
  let R : Set (OnePoint X) := range ((↑) : X → OnePoint X)
  let : PolishSpace R := OnePoint.isOpen_range_coe.polishSpace
  exact OnePoint.isOpenEmbedding_coe.toIsEmbedding.toHomeomorph.isClosedEmbedding.polishSpace

end AreaDeficit.Surfaces
