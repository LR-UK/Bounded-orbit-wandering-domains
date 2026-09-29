module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.AreaAdvanceOnCover
public import BoundedWanderingDomains.Surfaces.SingularEncounters.ControlledAreaCover
public import BoundedWanderingDomains.Surfaces.AlmostEverywhere.AreaBarrierModels
public import BoundedWanderingDomains.Surfaces.PositiveAreaAdvanceReduction
public import BoundedWanderingDomains.Surfaces.PositiveAreaExceptionalReduction
public import BoundedWanderingDomains.Surfaces.BarrierCompactOrbit
public import BoundedWanderingDomains.Surfaces.OmegaDynamics

@[expose] public section

/-! # Positive-area exclusion under finite component obstruction control -/

open Set Function Filter MeasureTheory Topology
open AreaDeficit.Surfaces
open scoped Manifold ENNReal

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

theorem no_compact_positive_hyperbolic_area_saturation_of_regular_covers
    (p : DiscCover X) (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A K : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A) (hpos : 0 < p.hyperbolicArea A)
    (hK : IsCompact K) (hsatK : f.saturation A ⊆ K)
    {ι : Type*} [Fintype ι] (D : ι → TopologicalSpace.Opens X) (E : Finset X)
    (L : ι → Set X) (hL : ∀ i, IsCompact (L i)) (hLD : ∀ i, L i ⊆ D i)
    (hcover : ∀ W : Set X, W.Nonempty → W ⊆ f.saturation A →
      (∀ x ∈ W, f.totalize x ∉ E) →
      ∃ (V : ℕ → TopologicalSpace.Opens X) (hV : ∀ n, (V n : Set X) ⊆ f.source)
        (label : ℕ → ι),
        (∀ n, (D (label n) : Set X) \ (E : Set X) ⊆
          (f.restrictSource (V n) (hV n)).regularValues) ∧
        W ⊆ ⋃ n, (V n : Set X) ∩ f.totalize ⁻¹' L (label n)) : False := by
  classical
  obtain ⟨P, hP, hfront, hPf, hPb, _⟩ :=
    f.exists_forward_source_finitePuncture_barrier hf f.isOpen_omega f.omega_subset_source
      (fun x hx => by
        have hh := f.totalize_mapsTo_omega hf hx
        rwa [f.totalize_eq (f.omega_subset_source hx)] at hh)
  have hAP : A ⊆ closure (⋃ n, (P n : Set X)) := by
    intro x hx
    by_contra hxP
    have hcomp := f.barrier_component_subset_omega_of_compact_orbit hf p
      isClosed_closure hfront hPb (hAbad hx).1 hxP hK
      (fun n => hsatK (mem_iUnion.mpr ⟨n, x, hx,
        f.iterate_eq_some_orbit n ⟨x, (hAbad hx).1⟩⟩))
    exact (hAbad hx).2 (hcomp (mem_connectedComponentIn hxP))
  obtain ⟨S, hScount, hPS, hES, hback⟩ :=
    f.exists_countable_backward_invariant_superset hf P E
  let Astar := A \ S
  let W := f.saturation Astar
  obtain ⟨hAstarm, hWm, hAW, hWK, hWinj, himage, hWS⟩ :=
    f.diff_backwardExceptional_wandering_configuration_basic hf hA
      (fun x hx => (hAbad hx).1) hdis hinj hsatK (subset_univ K) hScount
      (fun x _ hx => hback x hx)
  have hAstarpos : 0 < p.hyperbolicArea Astar := by
    rw [hyperbolicArea_diff_countable p A hScount]
    exact hpos
  have hAstarP : Astar ⊆ closure (⋃ n, (P n : Set X)) := sdiff_subset.trans hAP
  have hWA : W ⊆ f.saturation A := by
    intro y hy
    obtain ⟨n, x, hx, he⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨n, x, hx.1, he⟩
  have hWavoid : ∀ x ∈ W, f.totalize x ∉ S := by
    intro x hx
    apply disjoint_left.mp hWS
    have hh : f.totalize x ∈ f.totalize '' W := ⟨x, hx, rfl⟩
    rw [himage] at hh
    exact hh.1
  have hWne : W.Nonempty := by
    have hAstarne : Astar.Nonempty := by
      apply Set.nonempty_iff_ne_empty.mpr
      intro he
      simp only [he, measure_empty, lt_self_iff_false] at hAstarpos
    exact hAstarne.mono hAW
  obtain ⟨V, hV, label, hreg, hWcover⟩ := hcover W hWne hWA
    (fun x hx he => hWavoid x hx (hES he))
  obtain ⟨C, hC, hstep⟩ := f.exists_uniform_area_advance_on_countable_cover hf p D E L hL hLD
  apply false_of_positive_hyperbolicArea_area_advances p P hP hAstarm hAstarpos hAstarP 0 hK hC
  intro n
  refine ⟨∅, f.totalize, W, by simp, hAW, hWK, ?_, ?_, ?_⟩
  · rw [himage]
    exact hWm.diff hAstarm
  · rw [himage]
  · simpa only [Finset.union_empty] using
      hstep V hV label hreg (P n) (hPf n) W hWm hWinj hWcover (by
        intro x hx
        have hfWS := hWavoid x hx
        exact ⟨fun hp => hfWS (hPS n hp), fun he => hfWS (hES he)⟩)

theorem no_compact_positive_hyperbolic_area_saturation_of_finite_component_control
    (p : DiscCover X) (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A K : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A) (hpos : 0 < p.hyperbolicArea A)
    (hK : IsCompact K) (hsatK : f.saturation A ⊆ K)
    {ι : Type*} [Fintype ι] (D : ι → TopologicalSpace.Opens X) (E : Finset X)
    (L : ι → Set X) (hL : ∀ i, IsCompact (L i)) (hLD : ∀ i, L i ⊆ D i)
    (hD : ∀ i, IsConnected (D i : Set X))
    (hcontrol : ∀ x ∈ f.saturation A, ∃ i, f.totalize x ∈ L i ∧
      x ∈ f.finiteObstructionSource hf.2.continuous (D i) (E : Set X)) : False := by
  apply no_compact_positive_hyperbolic_area_saturation_of_regular_covers p f hf
    hA hAbad hdis hinj hpos hK hsatK D E L hL hLD
  intro W hWne hWA havoid
  exact f.countable_regular_cover_of_component_control hf D hD L E hWne
    (hWA.trans ((f.saturation_subset_trapped (fun x hx => (hAbad hx).1)).trans
      f.trapped_subset_source)) havoid (fun x hx => hcontrol x (hWA hx))

end SurfaceDynamics
