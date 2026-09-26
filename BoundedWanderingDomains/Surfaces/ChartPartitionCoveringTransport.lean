/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CountablePatchTransport
import BoundedWanderingDomains.Surfaces.CountableChartPartition
import BoundedWanderingDomains.Surfaces.SurfacePolish
import Mathlib.Data.Nat.Pairing

/-! # Covering transport from canonical countable chart partitions -/

open Set Function MeasureTheory
open scoped Manifold

namespace AreaDeficit.Surfaces.DiscCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [T2Space X] [LocallyCompactSpace X]

/-- A covering between open surface domains preserves intrinsic area on any
measurable set on which its ambient representative is injective. Countable
source/target chart partitions are constructed internally. -/
theorem domainArea_eq_image_of_openDomain_covering
    (p : DiscCover X) (U V : TopologicalSpace.Opens X)
    (F : U → V) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hcov : IsCoveringMap F)
    {f : X → X} (hf : (fun x : U => f x) = (fun x => (F x : X)))
    (hfm : Measurable f) {W : Set X} (hW : MeasurableSet W)
    (hWU : W ⊆ U) (hinj : InjOn f W) :
    p.domainArea U W = p.domainArea V (f '' W) := by
  letI : Nonempty X := ⟨p.projection ⟨0, by simp [unitDisc]⟩⟩
  letI : PolishSpace X := AreaDeficit.Surfaces.surfacePolishSpace
  let P := Classical.choice (AreaDeficit.Surfaces.exists_chartPartition (M := X))
  let Q := Classical.choice (AreaDeficit.Surfaces.exists_chartPartition (M := X))
  let uv : ℕ → ℕ × ℕ := Nat.unpair
  let c : ℕ → OpenPartialHomeomorph X ℂ := fun k => P.chart (uv k).1
  let d : ℕ → OpenPartialHomeomorph X ℂ := fun k => Q.chart (uv k).2
  let A : ℕ → Set X := fun k =>
    W ∩ P.piece (uv k).1 ∩ f ⁻¹' Q.piece (uv k).2
  have hA : ∀ k, MeasurableSet (A k) := by
    intro k
    exact (hW.inter (P.measurable _)).inter ((Q.measurable _).preimage hfm)
  have hsub : ∀ k, A k ⊆ W := fun _ _ hx => hx.1.1
  have hdis : Pairwise (Disjoint on A) := by
    intro i j hij
    have huv : uv i ≠ uv j := by
      intro he
      apply hij
      calc
        i = Nat.pair (uv i).1 (uv i).2 := (Nat.pair_unpair i).symm
        _ = Nat.pair (uv j).1 (uv j).2 := congrArg (fun z => Nat.pair z.1 z.2) he
        _ = j := Nat.pair_unpair j
    have hcoord : (uv i).1 ≠ (uv j).1 ∨ (uv i).2 ≠ (uv j).2 := by
      by_cases hfst : (uv i).1 = (uv j).1
      · exact Or.inr (fun hsnd => huv (Prod.ext hfst hsnd))
      · exact Or.inl hfst
    rcases hcoord with hfst | hsnd
    · apply Set.disjoint_left.mpr
      intro x hxi hxj
      exact Set.disjoint_left.mp (P.disjoint hfst) hxi.1.2 hxj.1.2
    · apply Set.disjoint_left.mpr
      intro x hxi hxj
      exact Set.disjoint_left.mp (Q.disjoint hsnd) hxi.2 hxj.2
  have hcover : (⋃ k, A k) = W := by
    apply Subset.antisymm
    · exact iUnion_subset hsub
    · intro x hxW
      have hxP : x ∈ ⋃ n, P.piece n := by rw [P.covers]; trivial
      obtain ⟨n, hxn⟩ := mem_iUnion.mp hxP
      have hxQ : f x ∈ ⋃ m, Q.piece m := by rw [Q.covers]; trivial
      obtain ⟨m, hxm⟩ := mem_iUnion.mp hxQ
      apply mem_iUnion.mpr
      refine ⟨Nat.pair n m, ?_⟩
      simpa only [A, uv, Nat.unpair_pair] using ⟨⟨hxW, hxn⟩, hxm⟩
  have hfA : ∀ k, MeasurableSet (f '' A k) := by
    have hfcont : ContinuousOn f U := by
      rw [continuousOn_iff_continuous_restrict]
      change Continuous (fun x : U => f x)
      rw [hf]
      exact continuous_subtype_val.comp hF.continuous
    intro k
    exact (hA k).image_of_continuousOn_injOn
      (hfcont.mono (fun _ hx => hWU (hsub k hx)))
      (hinj.mono (hsub k))
  apply p.domainArea_eq_image_of_openDomain_covering_countable_patches
    U V F hF hcov hf c d (fun k => P.holomorphic _) (fun k => Q.holomorphic _)
    A hA hfA
  · exact fun _ _ hx => hWU hx.1.1
  · exact fun k _ hx => P.subordinate _ hx.1.2
  · intro k
    rintro _ ⟨x, hx, rfl⟩
    exact Q.subordinate _ hx.2
  · exact hsub
  · exact hdis
  · exact hcover
  · exact hinj

end AreaDeficit.Surfaces.DiscCover

#print axioms AreaDeficit.Surfaces.DiscCover.domainArea_eq_image_of_openDomain_covering
