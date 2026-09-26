/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.LocalCompactModelPatches
import BoundedWanderingDomains.Surfaces.PositiveAreaFinalReduction
import Mathlib.Order.Disjointed

/-! # Compact local area advance from finitely many proper patches -/

open Set Function MeasureTheory Topology
open scoped Manifold Topology ENNReal

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X]
  [MeasurableSpace X] [BorelSpace X] [DecidableEq X]

/-- The local proper models cover a compact set and their area estimates
assemble after making the cover into a measurable disjoint partition. -/
theorem compactLocalAreaAdvanceClaim : CompactLocalAreaAdvanceClaim (X := X) := by
  intro p f hf V hVcompact hVsource K hK hKV
  have hpatch : ∀ x : K, ∃ (Ks L N : Set X),
      IsCompact Ks ∧ Ks ⊆ f.source ∧ IsCompact L ∧ Ks ⊆ V ∧
      IsOpen N ∧ (x : X) ∈ N ∧ N ⊆ interior Ks ∧
      f.totalize '' N ⊆ L ∧
      Disjoint L (f.map '' frontier (f.sourceCompact Ks)) := by
    intro x
    let xs : f.source :=
      ⟨(x : X), hVsource (subset_closure (hKV x.property))⟩
    simpa only [xs] using f.exists_local_compact_model_patch hf V xs (hKV x.property)
  choose Ks L N hKs hKssource hL hKsV hNopen hxN hNKs hfNL hsep using hpatch
  have hcoverK : K ⊆ ⋃ x : K, N x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxN ⟨x, hx⟩⟩
  obtain ⟨I, hcover⟩ := hK.elim_finite_subcover N hNopen hcoverK
  have hlocal : ∀ x : K, ∃ (E : Finset X) (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ (P : Finset X),
        (∀ y (hy : y ∈ V), y ∈ P →
          f.map ⟨y, hVsource (subset_closure hy)⟩ ∈ P) →
        ∀ W : Set X, MeasurableSet W → W ⊆ interior (Ks x) →
          InjOn f.totalize W → f.totalize '' W ⊆ L x →
          (∀ y ∈ W, f.totalize y ∉ P ∪ E ∧
            f.totalize y ∉ f.map '' frontier (f.sourceCompact (Ks x))) →
          p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain P) W ≤
            p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain P)
              (f.totalize '' W) + C := by
    intro x
    obtain ⟨E, -, hcore⟩ :=
      f.exists_uniform_area_advance_of_local_compact_finite_models p hf V
        (fun y hy => hVsource (subset_closure hy))
        (hKs x) (hKssource x) (hKsV x) (hL x)
    obtain ⟨C, hC, hstep⟩ := hcore (hsep x)
    exact ⟨E, C, hC, hstep⟩
  choose E C hC hstep using hlocal
  let Etot : Finset X := I.biUnion E
  let ι := {x : K // x ∈ I}
  let R : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let idx : Fin (Fintype.card ι) → K := fun i => (R i).val
  let Ctot : ℝ≥0∞ := ∑ i, C (idx i)
  refine ⟨Etot, Ctot, ?_, ?_⟩
  · simp only [Ctot, ENNReal.sum_ne_top]
    intro i _
    exact hC (idx i)
  intro P hforward W hW hWK hinj havoid
  let B : Fin (Fintype.card ι) → Set X := fun i => W ∩ N (idx i)
  let A : Fin (Fintype.card ι) → Set X := disjointed B
  have hB : ∀ i, MeasurableSet (B i) := fun i => hW.inter (hNopen (idx i)).measurableSet
  have hA : ∀ i, MeasurableSet (A i) :=
    fun i => disjointedRec (fun _ j ht => ht.diff (hB j)) (hB i)
  have hAsubB : ∀ i, A i ⊆ B i := disjointed_subset B
  have hAsubW : ∀ i, A i ⊆ W := fun i => (hAsubB i).trans inter_subset_left
  have hApart : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin (Fintype.card ι))) : Set _) A :=
    (disjoint_disjointed B).set_pairwise _
  have hBcover : (⋃ i, B i) = W := by
    apply Set.Subset.antisymm
    · exact iUnion_subset fun i => inter_subset_left
    · intro y hy
      have hyK : y ∈ K := hWK hy
      obtain ⟨x, hxI, hyN⟩ := Set.mem_iUnion₂.mp (hcover hyK)
      let xi : ι := ⟨x, hxI⟩
      let i : Fin (Fintype.card ι) := R.symm xi
      apply mem_iUnion.mpr
      refine ⟨i, hy, ?_⟩
      simpa only [B, idx, i, xi, Equiv.apply_symm_apply] using hyN
  have hAcover : (⋃ i ∈ (Finset.univ : Finset (Fin (Fintype.card ι))), A i) = W := by
    simp only [Finset.mem_univ, iUnion_true]
    rw [iUnion_disjointed, hBcover]
  have hsourceW : W ⊆ f.source :=
    hWK.trans (hKV.trans (fun y hy => hVsource (subset_closure hy)))
  have himageMeas : MeasurableSet (f.totalize '' W) := by
    letI : PolishSpace X := AreaDeficit.Surfaces.surfacePolishSpace
    exact hW.image_of_continuousOn_injOn
      ((f.continuousOn_totalize hf.2.continuous).mono hsourceW) hinj
  have hfiA : ∀ i, MeasurableSet (f.totalize '' A i) := by
    intro i
    letI : PolishSpace X := AreaDeficit.Surfaces.surfacePolishSpace
    exact (hA i).image_of_continuousOn_injOn
      ((f.continuousOn_totalize hf.2.continuous).mono
        ((hAsubW i).trans hsourceW))
      (hinj.mono (hAsubW i))
  have hassembled := AreaDeficit.Surfaces.finite_patch_area_advance
    (p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain P))
    (p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain P))
    (Finset.univ : Finset (Fin (Fintype.card ι))) A (fun i => C (idx i))
    (fun i _ => hA i) (fun i _ => hfiA i) (fun i _ => hAsubW i)
    hApart hAcover hinj (fun i _ => ?_)
  · calc
      p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain P) W
          ≤ p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain P)
              (f.totalize '' W) + ∑ i, C (idx i) := hassembled
      _ ≤ p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain (P ∪ Etot))
              (f.totalize '' W) + ∑ i, C (idx i) := by
        have hmono :
            p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain P)
                (f.totalize '' W) ≤
              p.domainArea
                (AreaDeficit.Surfaces.finitePunctureDomain (P ∪ Etot))
                (f.totalize '' W) := p.domainArea_mono_on
          (AreaDeficit.Surfaces.finitePunctureDomain_antitone
            (show P ⊆ P ∪ Etot from Finset.subset_union_left))
          himageMeas (by
          rintro y ⟨x, hx, rfl⟩ hmem
          exact havoid x hx hmem)
        exact add_le_add hmono le_rfl
      _ = p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain (P ∪ Etot))
              (f.totalize '' W) + Ctot := by
        rfl
  · apply hstep (idx i) P hforward (A i) (hA i)
    · exact (hAsubB i).trans (inter_subset_right.trans (hNKs (idx i)))
    · exact hinj.mono (hAsubW i)
    · exact (image_mono ((hAsubB i).trans inter_subset_right)).trans (hfNL (idx i))
    · intro y hy
      have hay := havoid y (hAsubW i hy)
      refine ⟨?_, ?_⟩
      · intro hm
        apply hay
        rcases Finset.mem_union.mp hm with hp | he
        · exact Finset.mem_union_left _ hp
        · exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨idx i, (R i).property, he⟩)
      · intro hh
        apply Set.disjoint_left.mp (hsep (idx i))
          (hfNL (idx i) ⟨y, (hAsubB i hy).2, rfl⟩) hh

/-- The positive-area conclusion on every surface supplied with a
holomorphic universal covering by the unit disc. -/
theorem noCompactPositiveAreaWanderingSetClaim_of_discCover
    (p : AreaDeficit.Surfaces.DiscCover X) :
    NoCompactPositiveAreaWanderingSetClaim (X := X) :=
  noCompactPositiveAreaWanderingSetClaim_of_discCover_areaAdvance p
    compactLocalAreaAdvanceClaim

end SurfaceDynamics

#print axioms SurfaceDynamics.compactLocalAreaAdvanceClaim
#print axioms SurfaceDynamics.noCompactPositiveAreaWanderingSetClaim_of_discCover
