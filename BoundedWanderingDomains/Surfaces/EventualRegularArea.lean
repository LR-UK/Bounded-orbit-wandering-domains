module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.RegularCoveringArea
public import BoundedWanderingDomains.Surfaces.FiniteModelDiscArea
public import BoundedWanderingDomains.Surfaces.FiniteModelArea
public import BoundedWanderingDomains.AreaCancellation
public import BoundedWanderingDomains.TrappedComponentCovering

@[expose] public section

/-! # The wandering-disc contradiction with remote singular values -/

open Set Function Filter MeasureTheory
open AreaDeficit.Surfaces
open scoped Manifold Topology ENNReal

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

theorem false_of_eventual_regular_wandering_discs
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (p : DiscCover X)
    (E : Finset X) {H L : Set X} (hH : IsClosed H) (hL : IsCompact L)
    (hLH : Disjoint L H) (hS : f.singularValues ⊆ H ∪ (E : Set X))
    (P : ℕ → Finset X) (hP : Monotone P)
    (hPforward : ∀ j (x : f.source), (x : X) ∈ P j → f.map x ∈ P j)
    (U : ℕ → TopologicalSpace.Opens X) (q : ∀ n, DiscCover (U n))
    (hUs : ∀ n, (U n : Set X) ⊆ f.source)
    (hcomp : ∀ n, (U n : Set X) = connectedComponentIn
      (closure (⋃ j, (P j : Set X)))ᶜ ((q n).projection discZero : X))
    (hdis : Pairwise (fun n m => Disjoint (U n : Set X) (U m)))
    (hforward : ∀ r : ℝ, r < 1 → ∀ n,
      MapsTo f.totalize
        ((fun z => ((q n).projection z : X)) '' {z : unitDisc | ‖(z : ℂ)‖ < r})
        ((fun z => ((q (n + 1)).projection z : X)) '' {z : unitDisc | ‖(z : ℂ)‖ < r}))
    (hcompact : ∀ r : ℝ, 0 < r → r < 1 → ∀ᶠ n in atTop,
      ((fun z => ((q n).projection z : X)) '' {z : unitDisc | ‖(z : ℂ)‖ < r}) ⊆ L)
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
  obtain ⟨C, hC, hstep⟩ := f.exists_uniform_singular_area_advance hf p E hH hL hLH hS
  have havoidE : ∀ᶠ n in atTop, Disjoint (U n : Set X) (E : Set X) :=
    AreaDeficit.eventually_disjoint_finite hdis E.finite_toSet
  let A := closure (⋃ j, (P j : Set X))
  have hUA : ∀ n, (U n : Set X) ⊆ Aᶜ := by
    intro n
    rw [hcomp n]
    exact connectedComponentIn_subset _ _
  apply AreaDeficit.no_uniform_disc_area_bound C.toReal
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
  have hWo : IsOpen W := isOpen_iUnion fun n => isOpen_iUnion fun _ => hDo n
  have hDW : D N ⊆ W := fun x hx => mem_iUnion₂.mpr ⟨N, le_rfl, hx⟩
  have hWL : W ⊆ L := by
    intro x hx
    obtain ⟨n, hn, hx⟩ := mem_iUnion₂.mp hx
    exact (hN n hn).1 hx
  have hWs : W ⊆ f.source := by
    intro x hx
    obtain ⟨n, hn, hx⟩ := mem_iUnion₂.mp hx
    exact hUs n (hDU n hx)
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
  have hPN : ∀ j, p.domainArea (finitePunctureDomain (P j)) (D N) ≤ C := by
    intro j
    have hadv := hstep (P j) (hPforward j) W hWo.measurableSet hWs hiW
      (himage.trans (sdiff_subset.trans hWL)) (by
        intro x hx
        obtain ⟨n, hn, hx⟩ := mem_iUnion₂.mp hx
        have hfx := hDU _ (hforward r hr1 n hx)
        exact ⟨fun hp => hUA _ hfx (subset_closure (mem_iUnion.mpr ⟨j, hp⟩)),
          fun he => disjoint_left.mp (hN (n + 1) (by omega)).2.2.2.2 hfx he⟩)
    have hh := AreaDeficit.finite_area_cancellation_le (D := 0) (hDo N).measurableSet hDW
      (p.finitePunctureDomain_area_subset_compact_finite (P j) hL hWL) himage hadv
      (by simp)
    simpa using hh
  obtain ⟨c, hc, hDc⟩ := (hN N le_rfl).2.2.2.1
  have hcentreA : ((q N).projection discZero : X) ∉ A :=
    hUA N ((q N).projection discZero).property
  have harea := p.disc_area_le_of_finite_model_bounds isClosed_closure P hP
    (fun j _ hx => subset_closure (mem_iUnion.mpr ⟨j, hx⟩)) rfl
    (U N) (q N) hcentreA (hcomp N) hc hr1 hDc (hN N le_rfl).2.1 hPN
  rwa [ENNReal.ofReal_toReal hC]

end SurfaceDynamics.LocalMap
