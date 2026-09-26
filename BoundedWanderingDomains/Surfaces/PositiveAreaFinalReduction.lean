/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.PositiveAreaAdvanceReduction
import BoundedWanderingDomains.Surfaces.PositiveAreaBarrierReduction
import BoundedWanderingDomains.Surfaces.PositiveAreaExceptionalReduction

/-! # Final reduction of the positive-area theorem to local metric comparison -/

open Set Function MeasureTheory
open scoped Manifold Topology ENNReal

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X]
  [MeasurableSpace X] [BorelSpace X] [DecidableEq X]

/-- The sole analytic statement still needed for Theorem 1.3(2): on a
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

/-- Once compact local area advance is available, every positive-area
wandering saturation on a disc-covered surface escapes compact subsets of
the source.  All boundary, exceptional-set, measurability, and cancellation
steps are discharged here. -/
theorem noCompactPositiveAreaWanderingSetClaim_of_discCover_areaAdvance
    (p : AreaDeficit.Surfaces.DiscCover X)
    (pTop : AreaDeficit.Surfaces.DiscCover (⊤ : TopologicalSpace.Opens X))
    (hadvance : CompactLocalAreaAdvanceClaim (X := X)) :
    NoCompactPositiveAreaWanderingSetClaim (X := X) := by
  intro f hf A hAmeas hAbad hdis hinj hApos
  rintro ⟨K, hK, hKsource, hsatK⟩
  let O : TopologicalSpace.Opens X := ⊤
  obtain ⟨V, hVsource, P, hKV, hVcompact, hPmono, hPforward,
      hArestrict, hAP⟩ :=
    f.exists_positiveArea_boundaryBarrier hf O pTop (fun _ _ => trivial)
      hAbad hK hKsource hsatK
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
      (fun _ hx => (hAbad hx).1) hdis hinj hsatK hKV hScount hback'
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

end SurfaceDynamics

#print axioms SurfaceDynamics.noCompactPositiveAreaWanderingSetClaim_of_discCover_areaAdvance
