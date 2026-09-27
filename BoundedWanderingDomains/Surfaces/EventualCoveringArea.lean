/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.FiniteModelDiscArea
import BoundedWanderingDomains.Surfaces.CompactLocalAreaAdvance
import BoundedWanderingDomains.Surfaces.WanderingDiscInjectivity

/-! # The area contradiction for eventually embedded wandering discs -/

open Set Function Filter MeasureTheory
open AreaDeficit.Surfaces
open scoped Manifold Topology ENNReal

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X]
  [MeasurableSpace X] [BorelSpace X] [DecidableEq X]

/-- Once the wandering discs embed and the map is injective on their tail,
finite-model cancellation bounds every disc radius by one fixed constant.
The exact disc-area formula contradicts this bound. -/
theorem false_of_eventual_wandering_covering_discs
    (p : DiscCover X) (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (V : TopologicalSpace.Opens X) (hVc : IsCompact (closure (V : Set X)))
    (hVsource : closure (V : Set X) ⊆ f.source)
    {K : Set X} (hK : IsCompact K) (hKV : K ⊆ V)
    (P : ℕ → Finset X) (hP : Monotone P)
    (hPforward : ∀ j x (hx : x ∈ V), x ∈ P j →
      f.map ⟨x, hVsource (subset_closure hx)⟩ ∈ P j)
    (U : ℕ → TopologicalSpace.Opens X) (q : ∀ n, DiscCover (U n))
    (hcomp : ∀ n, (U n : Set X) = connectedComponentIn
      (closure (⋃ j, (P j : Set X)))ᶜ ((q n).projection discZero : X))
    (hdis : Pairwise (fun n m => Disjoint (U n : Set X) (U m)))
    (hforward : ∀ r : ℝ, r < 1 → ∀ n,
      MapsTo f.totalize
        ((fun z => ((q n).projection z : X)) '' {z : unitDisc | ‖(z : ℂ)‖ < r})
        ((fun z => ((q (n + 1)).projection z : X)) '' {z : unitDisc | ‖(z : ℂ)‖ < r}))
    (hcompact : ∀ r : ℝ, 0 < r → r < 1 → ∀ᶠ n in atTop,
      ((fun z => ((q n).projection z : X)) '' {z : unitDisc | ‖(z : ℂ)‖ < r}) ⊆ K)
    (hpinj : ∀ r : ℝ, 0 < r → r < 1 → ∀ᶠ n in atTop,
      InjOn (q n).projection {z : unitDisc | ‖(z : ℂ)‖ < r})
    (hinj : ∀ r : ℝ, 0 < r → r < 1 → ∀ᶠ n in atTop,
      InjOn f.totalize ((fun z => ((q n).projection z : X)) ''
        {z : unitDisc | ‖(z : ℂ)‖ < r}))
    (hchart : ∀ r : ℝ, 0 < r → r < 1 → ∀ᶠ n in atTop,
      ∃ c : OpenPartialHomeomorph X ℂ,
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source ∧
        ∀ z : unitDisc, ‖(z : ℂ)‖ < r → ((q n).projection z : X) ∈ c.source) : False := by
  classical
  obtain ⟨E, C, hC, hstep⟩ := compactLocalAreaAdvanceClaim p f hf V hVc hVsource K hK hKV
  obtain ⟨H, hH, hcancel⟩ := p.finite_model_cancellation_of_area_advance E.card hK hC
  have havoidE : ∀ᶠ n in atTop, Disjoint (U n : Set X) (E : Set X) :=
    AreaDeficit.eventually_disjoint_finite hdis E.finite_toSet
  let A := closure (⋃ j, (P j : Set X))
  have hUA : ∀ n, (U n : Set X) ⊆ Aᶜ := by
    intro n
    rw [hcomp n]
    exact connectedComponentIn_subset _ _
  apply AreaDeficit.no_uniform_disc_area_bound H.toReal
  intro r hr hr1
  rcases hr.eq_or_lt with rfl | hr
  · simp
  let D : ℕ → Set X := fun n =>
    (fun z => ((q n).projection z : X)) '' {z : unitDisc | ‖(z : ℂ)‖ < r}
  have hDo : ∀ n, IsOpen (D n) := fun n =>
    ((U n).isOpen.isOpenMap_subtype_val.comp (q n).isOpenMap) _
      (isOpen_lt continuous_subtype_val.norm continuous_const)
  have hDU : ∀ n, D n ⊆ U n := by
    rintro n y ⟨z, hz, rfl⟩
    exact ((q n).projection z).property
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((hcompact r hr hr1).and ((hpinj r hr hr1).and
      ((hinj r hr hr1).and ((hchart r hr hr1).and havoidE))))
  let W := ⋃ n ≥ N, D n
  have hW : IsOpen W := isOpen_iUnion fun n => isOpen_iUnion fun _ => hDo n
  have hDW : D N ⊆ W := fun x hx => mem_iUnion₂.mpr ⟨N, le_rfl, hx⟩
  have hWK : W ⊆ K := by
    intro x hx
    obtain ⟨n, hn, hx⟩ := mem_iUnion₂.mp hx
    exact (hN n hn).1 hx
  have hiW : InjOn f.totalize W := by
    intro x hx y hy hxy
    obtain ⟨n, hn, hx⟩ := mem_iUnion₂.mp hx
    obtain ⟨m, hm, hy⟩ := mem_iUnion₂.mp hy
    have hnm : n = m := by
      by_contra hne
      exact disjoint_left.mp (hdis (by omega : n + 1 ≠ m + 1))
        (hDU _ (hforward r hr1 n hx)) (hxy ▸ hDU _ (hforward r hr1 m hy))
    subst m
    exact (hN n hn).2.2.1 hx hy hxy
  have himage : f.totalize '' W ⊆ W \ D N := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨n, hn, hx⟩ := mem_iUnion₂.mp hx
    refine ⟨mem_iUnion₂.mpr ⟨n + 1, by omega, hforward r hr1 n hx⟩, ?_⟩
    intro hy
    exact disjoint_left.mp (hdis (by omega : n + 1 ≠ N))
      (hDU _ (hforward r hr1 n hx)) (hDU _ hy)
  have himagemeas : MeasurableSet (f.totalize '' W) := by
    letI : PolishSpace X := AreaDeficit.Surfaces.surfacePolishSpace
    exact hW.measurableSet.image_of_continuousOn_injOn
      ((f.continuousOn_totalize hf.2.continuous).mono
        (hWK.trans (hKV.trans (subset_closure.trans hVsource)))) hiW
  have hPN : ∀ j, p.domainArea (finitePunctureDomain (P j)) (D N) ≤ H := by
    intro j
    apply hcancel (P j) E le_rfl f.totalize (D N) W (hDo N).measurableSet hDW hWK
      himagemeas himage
    apply hstep (P j) (hPforward j) W hW.measurableSet hWK hiW
    intro x hx hmem
    obtain ⟨n, hn, hx⟩ := mem_iUnion₂.mp hx
    have hfx := hDU _ (hforward r hr1 n hx)
    rcases Finset.mem_union.mp hmem with hp | he
    · exact hUA _ hfx (subset_closure (mem_iUnion.mpr ⟨j, hp⟩))
    · exact disjoint_left.mp (hN (n + 1) (by omega)).2.2.2.2 hfx he
  obtain ⟨c, hc, hDc⟩ := (hN N le_rfl).2.2.2.1
  have hcentreA : ((q N).projection discZero : X) ∉ A :=
    hUA N ((q N).projection discZero).property
  have harea := p.disc_area_le_of_finite_model_bounds isClosed_closure P hP
    (fun j _ hx => subset_closure (mem_iUnion.mpr ⟨j, hx⟩)) rfl
    (U N) (q N) hcentreA (hcomp N) hc hr1 hDc (hN N le_rfl).2.1 hPN
  rwa [ENNReal.ofReal_toReal hH]

end SurfaceDynamics.LocalMap
