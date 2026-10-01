module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.EncounterData

@[expose] public section

/-! # Pulling an encounter itinerary back by one iterate -/

open Set Function Filter Topology

namespace SurfaceDynamics.LocalMap

theorem HasSingularEncounterSequenceAt.pullback_one_step
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (f : LocalMap X) (hf : Continuous f.map) {W A : Set X} {z : f.trapped} {x : X}
    (h : f.HasSingularEncounterSequenceAt hf W (f.trappedMap z) x)
    (hAs : A ⊆ f.source) (hAW : MapsTo f.totalize A W) :
    f.HasSingularEncounterSequenceAt hf A z x := by
  obtain ⟨Q, φ, s, hφ, hs, hQ, hshrink, hsingular, hcapture⟩ := h
  have hshift : ∀ m, f.orbit m (f.trappedMap z) = f.orbit (m + 1) z := by
    intro m
    change ((f.trappedMap^[m]) (f.trappedMap z) : X) = ((f.trappedMap^[m + 1]) z : X)
    rw [Function.iterate_succ_apply]
  refine ⟨Q, fun n => φ n + 1, s, ?_, hs, hQ, hshrink, ?_, ?_⟩
  · intro n m hnm
    exact Nat.add_lt_add_right (hφ hnm) 1
  · intro n
    simpa only [hshift] using hsingular n
  · intro L hL hLA
    have hLi : IsCompact (f.totalize '' L) :=
      hL.image_of_continuousOn ((f.continuousOn_totalize hf).mono (hLA.trans hAs))
    have hLiW : f.totalize '' L ⊆ W := (hAW.mono_left hLA).image_subset
    filter_upwards [hcapture (f.totalize '' L) hLi hLiW] with n hn
    intro y hy
    simpa only [Function.iterate_succ_apply, hshift] using hn ⟨y, hy, rfl⟩

theorem HasSingularEncounterSequenceAt.pullback_along_components
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (f : LocalMap X) (hf : Continuous f.map) (W : ℕ → Set X)
    (hWs : ∀ n, W n ⊆ f.source) (hforward : ∀ n, MapsTo f.totalize (W n) (W (n + 1)))
    {z : f.trapped} {x : X} (N : ℕ)
    (h : f.HasSingularEncounterSequenceAt hf (W N) (f.trappedMap^[N] z) x) :
    f.HasSingularEncounterSequenceAt hf (W 0) z x := by
  induction N with
  | zero => exact h
  | succ N ih =>
    apply ih
    apply HasSingularEncounterSequenceAt.pullback_one_step f hf
      (z := f.trappedMap^[N] z) _ (hWs N) (hforward N)
    simpa only [iterate_succ_apply'] using h

end SurfaceDynamics.LocalMap
