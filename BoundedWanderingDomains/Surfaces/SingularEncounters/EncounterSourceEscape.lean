module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.CompactComponentObstructions
public import BoundedWanderingDomains.Surfaces.SingularEncounters.EncounterConsequences
public import BoundedWanderingDomains.Surfaces.LocalCompactModelPatches
public import BoundedWanderingDomains.Surfaces.CompactFilling
public import BoundedWanderingDomains.Surfaces.CompactificationEscape

@[expose] public section

/-! # Source escape forced by distinct shrinking component obstructions -/

open Set Function Filter Topology
open AreaDeficit.Surfaces
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [LocallyCompactSpace X] [T2Space X] [DecidableEq X]

theorem no_source_limit_of_distinct_shrinking_component_obstructions
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (D : ℕ → TopologicalSpace.Opens X) (c : ℕ → f.source) (s : ℕ → X)
    (hinj : Injective s) (b : f.source) (hc : Tendsto c atTop (𝓝 b))
    (hshrink : ∀ O ∈ 𝓝 (f.map b), ∀ᶠ n in atTop, (D n : Set X) ⊆ O)
    (hs : ∀ n, s n ∈ f.componentSingularValues hf.2.continuous (D n) (c n)) : False := by
  obtain ⟨K, L, N, hK, hKs, hL, _, hNo, hbN, hNK, hfN, hLH⟩ :=
    f.exists_local_compact_model_patch hf f.source b b.2
  obtain ⟨E, hE⟩ := f.exists_finite_component_obstructions_in_compact hf hK hKs
  let H := f.map '' frontier (f.sourceCompact K)
  have hH : IsCompact H := by
    apply ((f.sourceCompact_isCompact hK hKs).of_isClosed_subset isClosed_frontier
      (f.sourceCompact_isCompact hK hKs).isClosed.frontier_subset).image hf.2.continuous
  have hfbL : f.map b ∈ L := by
    have hh := hfN ⟨b, hbN, rfl⟩
    simpa only [f.totalize_eq b.2] using hh
  have hfbH : f.map b ∉ H := fun h => disjoint_left.mp hLH hfbL h
  let F : Set X := (E : Set X) \ {f.map b}
  have hF : IsClosed F := (E.finite_toSet.subset sdiff_subset).isClosed
  have hfbF : f.map b ∉ F := fun h => h.2 (mem_singleton _)
  have hD := hshrink (H ∪ F)ᶜ
    ((hH.isClosed.union hF).isOpen_compl.mem_nhds (fun h => h.elim hfbH hfbF))
  have hN := (continuous_subtype_val.continuousAt.tendsto.comp hc).eventually
    (hNo.mem_nhds hbN)
  have hneq : ∀ᶠ n in atTop, s n ≠ f.map b := by
    have hh := hinj.tendsto_cofinite.eventually (show {f.map b}ᶜ ∈ cofinite from
      (finite_singleton (f.map b)).compl_mem_cofinite)
    rw [Nat.cofinite_eq_atTop] at hh
    exact hh
  obtain ⟨n, hnD, hnN, hns⟩ := (hD.and (hN.and hneq)).exists
  have haD := f.base_map_mem_of_component_singular_value hf.2.continuous (D n) (c n) (hs n)
  have hDnH : (D n : Set X) ⊆ Hᶜ := fun _ hy hh => hnD hy (Or.inl hh)
  let C := connectedComponentIn (f.map ⁻¹' (D n : Set X)) (c n)
  have hCint : C ⊆ interior (f.sourceCompact K) := by
    apply preconnected_subset_open_of_avoids_frontier isPreconnected_connectedComponentIn
      isOpen_interior
    · apply disjoint_left.mpr
      intro u hu huf
      exact hDnH (connectedComponentIn_subset (f.map ⁻¹' (D n : Set X)) (c n) hu)
        ⟨u, frontier_interior_subset huf, rfl⟩
    · exact ⟨c n, mem_connectedComponentIn haD,
        preimage_interior_subset_interior_preimage continuous_subtype_val (hNK hnN)⟩
  have hC : (f.inverseComponentSource hf.2.continuous (D n) (c n) : Set X) ⊆ interior K := by
    rintro u ⟨v, hv, rfl⟩
    exact f.source.isOpen.isOpenMap_subtype_val.interior_preimage_subset_preimage_interior
      (hCint hv)
  have hsE := hE (D n) (c n) haD hDnH hC (hs n)
  exact hnD (hs n).2 (Or.inr ⟨hsE, hns⟩)

variable [SecondCountableTopology X]

/-- The source points of distinct singular encounters leave every compact
subset of the domain, along the selected encounter sequence. -/
theorem source_escape_of_distinct_shrinking_component_obstructions
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (D : ℕ → TopologicalSpace.Opens X) (c : ℕ → f.source) (s : ℕ → X)
    (hinj : Injective s) {x : X}
    (hshrink : ∀ O ∈ 𝓝 x, ∀ᶠ n in atTop, (D n : Set X) ⊆ O)
    (hs : ∀ n, s n ∈ f.componentSingularValues hf.2.continuous (D n) (c n))
    {K : Set X} (hK : IsCompact K) (hKs : K ⊆ f.source) :
    ∀ᶠ n in atTop, (c n : X) ∉ K := by
  by_contra hno
  have hfreq : ∃ᶠ n in atTop, c n ∈ f.sourceCompact K := by
    change ∃ᶠ n in atTop, (c n : X) ∈ K
    simpa only [not_not] using not_eventually.mp hno
  obtain ⟨b, _, ψ, hψ, hb⟩ := (f.sourceCompact_isCompact hK hKs).tendsto_subseq' hfreq
  have hmap : Tendsto (fun n => f.map (c n)) atTop (𝓝 x) := by
    apply tendsto_def.mpr
    intro O hO
    filter_upwards [hshrink O hO] with n hn
    exact hn (f.base_map_mem_of_component_singular_value hf.2.continuous (D n) (c n) (hs n))
  have hbx : f.map b = x := tendsto_nhds_unique
    (hf.2.continuous.continuousAt.tendsto.comp hb) (hmap.comp hψ.tendsto_atTop)
  apply f.no_source_limit_of_distinct_shrinking_component_obstructions hf
    (D ∘ ψ) (c ∘ ψ) (s ∘ ψ) (hinj.comp hψ.injective) b hb
  · intro O hO
    exact hψ.tendsto_atTop.eventually (hshrink O (hbx ▸ hO))
  · exact fun n => hs (ψ n)

theorem HasSingularEncounterSequenceAt.source_escaping_subsequence
    (f : LocalMap X) (hf : IsOpenHolomorphic f) {W : Set X} {z : f.trapped} {x : X}
    (h : f.HasSingularEncounterSequenceAt hf.2.continuous W z x) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ K : Set X, IsCompact K → K ⊆ f.source →
      ∀ᶠ n in atTop, f.orbit (φ n) z ∉ K := by
  obtain ⟨Q, φ, s, hφ, hs, _, hshrink, hsing, _⟩ := h
  refine ⟨φ, hφ, ?_⟩
  intro K hK hKs
  exact f.source_escape_of_distinct_shrinking_component_obstructions hf
    (fun n => (Q n).carrier) (fun n => ⟨f.orbit (φ n) z, f.orbit_mem_source (φ n) z⟩)
    s hs hshrink hsing hK hKs

end SurfaceDynamics.LocalMap
