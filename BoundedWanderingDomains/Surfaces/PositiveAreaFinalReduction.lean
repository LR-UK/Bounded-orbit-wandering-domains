module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.PositiveAreaAdvanceReduction
public import BoundedWanderingDomains.Surfaces.PositiveAreaBarrierReduction
public import BoundedWanderingDomains.Surfaces.PositiveAreaExceptionalReduction
public import BoundedWanderingDomains.Surfaces.TopDiscCover

@[expose] public section

/-! # Final reduction of the positive-area theorem to local metric comparison -/

open Set Function MeasureTheory
open scoped Manifold Topology ENNReal

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X]
  [MeasurableSpace X] [BorelSpace X] [DecidableEq X]

/-- The analytic area estimate used for the positive-area wandering-set theorem: on a
relatively compact local source, the hyperbolic area lost under one
holomorphic step is bounded uniformly over all forward-invariant finite
puncture models.  The finite exceptional set contains the branch values on
the compact model. -/
def CompactLocalAreaAdvanceClaim : Prop :=
  ∀ (p : AreaDeficit.Surfaces.DiscCover X) (f : LocalMap X),
    IsOpenHolomorphic f →
    ∀ (V : TopologicalSpace.Opens X),
      IsCompact (closure (V : Set X)) →
      ∀ (hVsource : closure (V : Set X) ⊆ f.source)
        (K : Set X), IsCompact K → K ⊆ V →
      ∃ (E : Finset X) (C : ℝ≥0∞), C ≠ ⊤ ∧
        ∀ (P : Finset X),
          (∀ x (hx : x ∈ V), x ∈ P →
            f.map ⟨x, hVsource (subset_closure hx)⟩ ∈ P) →
          ∀ (W : Set X), MeasurableSet W → W ⊆ K →
            InjOn f.totalize W →
            (∀ x ∈ W, f.totalize x ∉ P ∪ E) →
            p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain P) W ≤
              p.domainArea
                (AreaDeficit.Surfaces.finitePunctureDomain (P ∪ E))
                (f.totalize '' W) + C

omit [ConnectedSpace X] in
/-- The boundary-barrier contradiction using intrinsic area positivity
directly.  This is the form used after moving the compact dynamics into a
hyperbolic open subsurface. -/
theorem false_of_positiveHyperbolicArea_boundaryBarrier
    (p : AreaDeficit.Surfaces.DiscCover X)
    (hadvance : CompactLocalAreaAdvanceClaim (X := X))
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A K : Set X} (hAmeas : MeasurableSet A)
    (hAarea : 0 < p.hyperbolicArea A) (hAtrap : A ⊆ f.trapped)
    (hdis : Pairwise
      (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A)
    (hK : IsCompact K) (hsatK : f.saturation A ⊆ K)
    (V : TopologicalSpace.Opens X)
    (hVsource : closure (V : Set X) ⊆ f.source)
    (P : ℕ → Finset X) (hKV : K ⊆ V)
    (hVcompact : IsCompact (closure (V : Set X)))
    (hPmono : Monotone P)
    (hPforward : ∀ n x (hx : x ∈ V), x ∈ P n →
      f.map ⟨x, hVsource (subset_closure hx)⟩ ∈ P n)
    (hAP : A ⊆ closure (⋃ n, ((P n : Finset X) : Set X))) : False := by
  obtain ⟨E, C, hC, hstep⟩ :=
    hadvance p f hf V hVcompact hVsource K hK hKV
  obtain ⟨S, hSmono, hcontain, _hforward, hback⟩ :=
    f.exists_backwardExceptionalFinsets hf V hVcompact hVsource
      P hPmono E
  let Sstar : Set X := ⋃ n, ((S n : Finset X) : Set X)
  let Astar : Set X := A \ Sstar
  let Wstar : Set X := f.saturation Astar
  have hScount : Sstar.Countable :=
    Set.countable_iUnion fun n => (S n).finite_toSet.countable
  have hAstarmeas : MeasurableSet Astar :=
    hAmeas.diff hScount.measurableSet
  have hAstararea : 0 < p.hyperbolicArea Astar := by
    rw [SurfaceDynamics.hyperbolicArea_diff_countable p A hScount]
    exact hAarea
  have hPS : (⋃ n, ((P n : Finset X) : Set X)) ⊆ Sstar := by
    intro x hx
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n, (hcontain n).1 hxn⟩
  have hAstarP : Astar ⊆
      closure (⋃ n, ((P n : Finset X) : Set X)) :=
    sdiff_subset.trans hAP
  have hback' : ∀ (x : f.source), (x : X) ∈ V →
      f.map x ∈ Sstar → (x : X) ∈ Sstar := by
    intro x hx hfx
    exact hback (x : X) hx hfx
  obtain ⟨_, hWmeas, hAstarW, hWK, hWinj, himage, hWdis⟩ :=
    f.diff_backwardExceptional_wandering_configuration_basic hf hAmeas
      hAtrap hdis hinj hsatK hKV hScount hback'
  have himagemeas : MeasurableSet (f.totalize '' Wstar) := by
    rw [himage]
    exact hWmeas.diff hAstarmeas
  apply false_of_positive_hyperbolicArea_area_advances p P hPmono
    hAstarmeas hAstararea hAstarP E.card hK hC
  intro n
  refine ⟨E, f.totalize, Wstar, le_rfl, hAstarW, hWK,
    himagemeas, ?_, ?_⟩
  · rw [himage]
  · apply hstep (P n) (hPforward n) Wstar hWmeas hWK hWinj
    intro x hx
    have himageW : f.totalize x ∈ Wstar := by
      have hxi : f.totalize x ∈ f.totalize '' Wstar := ⟨x, hx, rfl⟩
      rw [himage] at hxi
      exact hxi.1
    have hnotS : f.totalize x ∉ Sstar :=
      Set.disjoint_left.mp hWdis himageW
    intro hmem
    rcases Finset.mem_union.mp hmem with hp | he
    · exact hnotS (mem_iUnion.mpr ⟨n, (hcontain n).1 hp⟩)
    · exact hnotS (mem_iUnion.mpr ⟨n, (hcontain n).2 he⟩)

omit [ConnectedSpace X] in
/-- The area contradiction after the boundary barrier has already been
constructed.  This form is stable under passing to a fixed hyperbolic open
subsurface: normality is used only to obtain `hAP`, and does not occur in the
remaining argument. -/
theorem false_of_positiveArea_boundaryBarrier
    (p : AreaDeficit.Surfaces.DiscCover X)
    (hadvance : CompactLocalAreaAdvanceClaim (X := X))
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A K : Set X} (hAmeas : MeasurableSet A)
    (hAtrap : A ⊆ f.trapped)
    (hdis : Pairwise
      (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A) (hApos : HasPositiveChartArea A)
    (hK : IsCompact K) (hsatK : f.saturation A ⊆ K)
    (V : TopologicalSpace.Opens X)
    (hVsource : closure (V : Set X) ⊆ f.source)
    (P : ℕ → Finset X) (hKV : K ⊆ V)
    (hVcompact : IsCompact (closure (V : Set X)))
    (hPmono : Monotone P)
    (hPforward : ∀ n x (hx : x ∈ V), x ∈ P n →
      f.map ⟨x, hVsource (subset_closure hx)⟩ ∈ P n)
    (hAP : A ⊆ closure (⋃ n, ((P n : Finset X) : Set X))) : False := by
  obtain ⟨E, C, hC, hstep⟩ :=
    hadvance p f hf V hVcompact hVsource K hK hKV
  obtain ⟨S, hSmono, hcontain, hback, hAstarmeas, hAstarpos,
      hAstarP, hAstarS⟩ :=
    f.exists_backwardExceptional_positive_remainder hf V hVcompact
      hVsource P hPmono E hAmeas hApos hAP
  let Sstar : Set X := ⋃ n, ((S n : Finset X) : Set X)
  let Astar : Set X := A \ Sstar
  let Wstar : Set X := f.saturation Astar
  have hScount : Sstar.Countable :=
    Set.countable_iUnion fun n => (S n).finite_toSet.countable
  have hback' : ∀ (x : f.source), (x : X) ∈ V →
      f.map x ∈ Sstar → (x : X) ∈ Sstar := by
    intro x hx hfx
    exact hback (x : X) hx hfx
  obtain ⟨_, _, hWmeas, hAstarW, hWK, hWinj, himage, hWdis⟩ :=
    f.diff_backwardExceptional_wandering_configuration hf hAmeas hApos
      hAtrap hdis hinj hsatK hKV hScount hback'
  have himagemeas : MeasurableSet (f.totalize '' Wstar) := by
    rw [himage]
    exact hWmeas.diff hAstarmeas
  apply false_of_positive_area_area_advances p P hPmono hAstarmeas
    hAstarpos hAstarP E.card hK hC
  intro n
  refine ⟨E, f.totalize, Wstar, le_rfl, hAstarW, hWK,
    himagemeas, ?_, ?_⟩
  · rw [himage]
  · apply hstep (P n) (hPforward n) Wstar hWmeas hWK hWinj
    intro x hx
    have himageW : f.totalize x ∈ Wstar := by
      have hxi : f.totalize x ∈ f.totalize '' Wstar := ⟨x, hx, rfl⟩
      rw [himage] at hxi
      exact hxi.1
    have hnotS : f.totalize x ∉ Sstar :=
      Set.disjoint_left.mp hWdis himageW
    intro hmem
    rcases Finset.mem_union.mp hmem with hp | he
    · exact hnotS (mem_iUnion.mpr ⟨n, (hcontain n).1 hp⟩)
    · exact hnotS (mem_iUnion.mpr ⟨n, (hcontain n).2 he⟩)

omit [ConnectedSpace X] in
/-- Once compact local area advance is available, every positive-area
wandering saturation on a disc-covered surface escapes compact subsets of
the source.  All boundary, exceptional-set, measurability, and cancellation
steps are discharged here. -/
theorem noCompactPositiveAreaWanderingSetClaim_of_discCover_areaAdvance
    (p : AreaDeficit.Surfaces.DiscCover X)
    (hadvance : CompactLocalAreaAdvanceClaim (X := X)) :
    NoCompactPositiveAreaWanderingSetClaim (X := X) := by
  intro f hf A hAmeas hAbad hdis hinj hApos
  rintro ⟨K, hK, hKsource, hsatK⟩
  let O : TopologicalSpace.Opens X := ⊤
  obtain ⟨V, hVsource, P, hKV, hVcompact, hPmono, hPforward,
      hArestrict, hAP⟩ :=
    f.exists_positiveArea_boundaryBarrier hf O p.top (fun _ _ => trivial)
      hAbad hK hKsource hsatK
  exact false_of_positiveArea_boundaryBarrier p hadvance f hf hAmeas
    (fun x hx => (hAbad hx).1) hdis hinj hApos hK hsatK V hVsource P
    hKV hVcompact hPmono hPforward hAP

omit [ConnectedSpace X] in
/-- Intrinsic-area version of the disc-covered conclusion. -/
theorem noCompactPositiveHyperbolicAreaWanderingSet_of_discCover_areaAdvance
    (p : AreaDeficit.Surfaces.DiscCover X)
    (hadvance : CompactLocalAreaAdvanceClaim (X := X)) :
    ∀ (f : LocalMap X), IsOpenHolomorphic f →
      ∀ (A : Set X), MeasurableSet A → A ⊆ f.trapped \ f.omega →
        Pairwise (fun n m : ℕ =>
          Disjoint (f.imageAt n A) (f.imageAt m A)) →
        f.InjectiveOnSaturation A → 0 < p.hyperbolicArea A →
        ¬ ∃ K : Set X, IsCompact K ∧ K ⊆ f.source ∧
          f.saturation A ⊆ K := by
  intro f hf A hAmeas hAbad hdis hinj hAarea
  rintro ⟨K, hK, hKsource, hsatK⟩
  let O : TopologicalSpace.Opens X := ⊤
  obtain ⟨V, hVsource, P, hKV, hVcompact, hPmono, hPforward,
      hArestrict, hAP⟩ :=
    f.exists_positiveArea_boundaryBarrier hf O p.top (fun _ _ => trivial)
      hAbad hK hKsource hsatK
  exact false_of_positiveHyperbolicArea_boundaryBarrier p hadvance f hf
    hAmeas hAarea (fun x hx => (hAbad hx).1) hdis hinj hK hsatK
    V hVsource P hKV hVcompact hPmono hPforward hAP

end SurfaceDynamics
