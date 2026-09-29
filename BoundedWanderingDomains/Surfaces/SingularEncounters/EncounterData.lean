module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.InverseComponents
public import BoundedWanderingDomains.Surfaces.SingularEncounters.EmbeddedDisc
public import BoundedWanderingDomains.Surfaces.LocalMapTotalization
public import Mathlib.Topology.DerivedSet

@[expose] public section

/-! # The combined singular-encounter conclusion -/

open Set Function Filter Topology
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Distinct genuine singular values in shrinking target discs, with full
inverse components that eventually capture each compact part of the initial
set at a common increasing sequence of times. -/
def HasSingularEncounterSequenceAt (f : LocalMap X) (hf : Continuous f.map)
    (W : Set X) (z : f.trapped) (x : X) : Prop :=
  ∃ (Q : ℕ → EmbeddedDisc X) (φ : ℕ → ℕ) (s : ℕ → X),
    StrictMono φ ∧ Injective s ∧ (∀ n, x ∈ (Q n).carrier) ∧
    (∀ O ∈ 𝓝 x, ∀ᶠ n in atTop, ((Q n).carrier : Set X) ⊆ O) ∧
    (∀ n, s n ∈ f.componentSingularValues hf
      (Q n).carrier
      ⟨f.orbit (φ n) z, f.orbit_mem_source (φ n) z⟩) ∧
    ∀ L : Set X, IsCompact L → L ⊆ W → ∀ᶠ n in atTop,
      MapsTo (f.totalize^[φ n]) L
        (f.inverseComponentSource hf
          (Q n).carrier
          ⟨f.orbit (φ n) z, f.orbit_mem_source (φ n) z⟩)

theorem derived_mem_of_shrinking_component_obstructions
    [T2Space X] [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) (hf : Continuous f.map) (c : ℕ → f.source)
    (D : ℕ → TopologicalSpace.Opens X) (s : ℕ → X) {x : X}
    (hinj : Injective s)
    (hshrink : ∀ O ∈ 𝓝 x, ∀ᶠ n in atTop, (D n : Set X) ⊆ O)
    (hs : ∀ n, s n ∈ f.componentSingularValues hf (D n) (c n)) :
    Tendsto s atTop (𝓝 x) ∧ x ∈ derivedSet f.singularValues := by
  have hlim : Tendsto s atTop (𝓝 x) := by
    apply tendsto_def.mpr
    intro O hO
    filter_upwards [hshrink O hO] with n hn
    exact hn (hs n).2
  refine ⟨hlim, ?_⟩
  by_contra hn
  have he := hlim.eventually (not_frequently.mp
    (fun hfreq => hn (accPt_iff_frequently.mpr hfreq)))
  have heq : ∀ᶠ n in atTop, s n = x := by
    filter_upwards [he] with n hn
    by_contra hne
    exact hn ⟨hne, f.componentSingularValues_subset hf _ _ (hs n)⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp heq
  have hbad := hinj ((hN N le_rfl).trans (hN (N + 1) (Nat.le_succ N)).symm)
  omega

theorem derived_mem_of_shrinking_component_singular_values
    [T2Space X] [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) (hf : Continuous f.map) (c : ℕ → f.source)
    (Q : ℕ → RiemannDynamics.CoordDisk X) (s : ℕ → X) {x : X}
    (hinj : Injective s)
    (hshrink : ∀ O ∈ 𝓝 x, ∀ᶠ n in atTop, (Q n).closedCarrier ⊆ O)
    (hs : ∀ n, s n ∈ f.componentSingularValues hf
      ⟨range (Q n).param, (Q n).isOpenEmbedding_param.isOpen_range⟩ (c n)) :
    Tendsto s atTop (𝓝 x) ∧ x ∈ derivedSet f.singularValues := by
  apply f.derived_mem_of_shrinking_component_obstructions hf c
    (fun n => ⟨range (Q n).param, (Q n).isOpenEmbedding_param.isOpen_range⟩) s hinj _ hs
  intro O hO
  filter_upwards [hshrink O hO] with n hn
  rintro y ⟨w, rfl⟩
  exact hn ((Q n).param_mem_closedCarrier w)

theorem HasSingularEncounterSequenceAt.derived_mem
    [T2Space X] [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) (hf : Continuous f.map) {W : Set X} {z : f.trapped} {x : X}
    (h : f.HasSingularEncounterSequenceAt hf W z x) : x ∈ derivedSet f.singularValues := by
  obtain ⟨Q, φ, s, _, hs, _, hshrink, hsing, _⟩ := h
  exact (f.derived_mem_of_shrinking_component_obstructions hf
    (fun n => ⟨f.orbit (φ n) z, f.orbit_mem_source (φ n) z⟩)
    (fun n => (Q n).carrier) s hs hshrink hsing).2

end SurfaceDynamics.LocalMap
