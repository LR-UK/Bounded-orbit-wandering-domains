/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.LocalCompactCovering
import BoundedWanderingDomains.Surfaces.RemoteCoveringAreaAdvance
import BoundedWanderingDomains.Surfaces.SaturationDynamics

/-! # Uniform area advance for a compact local-map model -/

open Set Function MeasureTheory
open scoped Manifold ENNReal Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [LocallyCompactSpace X] [T2Space X]
  [DecidableEq X]

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) 1 X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [LocallyCompactSpace X] [DecidableEq X] in
/-- Forward invariance of an old finite puncture set inside the working
domain is exactly what makes the compact covering source a subdomain of the
old punctured model. -/
theorem localCompactCoverDomain_le_finitePunctureDomain
    (f : LocalMap X) (hf : Continuous f.map)
    (V : TopologicalSpace.Opens X) (hVsource : (V : Set X) ⊆ f.source)
    {K : Set X} (hKV : K ⊆ V)
    (P E : Finset X)
    (hforward : ∀ x (hx : x ∈ V), x ∈ P →
      f.map ⟨x, hVsource hx⟩ ∈ P)
    (H : Set X) (hH : IsClosed H) :
    let U := AreaDeficit.Surfaces.finitePunctureDomain P
    let S := AreaDeficit.Surfaces.finiteRemovalDomain U E ⊓
      (⟨Hᶜ, hH.isOpen_compl⟩ : TopologicalSpace.Opens X)
    f.localCompactCoverDomain K S hf ≤ U := by
  dsimp only
  intro x hx
  obtain ⟨w, hw, heq⟩ := hx
  have hwK : (w : X) ∈ K := by
    have hwKs : w ∈ f.sourceCompact K := interior_subset hw.1
    exact hwKs
  have hwV : (w : X) ∈ V := hKV hwK
  have hfwP : f.map w ∉ P := hw.2.1.1
  change (x : X) ∉ P
  intro hxP
  have hwP : (w : X) ∈ P := heq ▸ hxP
  apply hfwP
  have h := hforward (w : X) hwV hwP
  simpa only using h

/-- The compact local covering construction and the uniform remote-removal
estimate combine into the exact one-step inequality used in finite-model
cancellation.  Backward invariance of the old punctures appears only as the
natural inclusion `T ≤ U`. -/
theorem exists_uniform_area_advance_of_local_compact_model
    (p : AreaDeficit.Surfaces.DiscCover X)
    (f : LocalMap X) (hf : IsOpenHolomorphic f) {K L : Set X}
    (hK : IsCompact K) (hKsource : K ⊆ f.source) (hL : IsCompact L) :
    ∃ (E : Finset X),
      IsCompact (f.map '' frontier (f.sourceCompact K)) ∧
      (Disjoint L (f.map '' frontier (f.sourceCompact K)) →
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
        ∀ U : TopologicalSpace.Opens X,
          let S := AreaDeficit.Surfaces.finiteRemovalDomain U E ⊓
            (⟨(f.map '' frontier (f.sourceCompact K))ᶜ, (by
              have hKs := f.sourceCompact_isCompact hK hKsource
              have hfront : IsCompact (frontier (f.sourceCompact K)) := by
                apply hKs.of_isClosed_subset isClosed_frontier
                simpa only [hKs.isClosed.closure_eq] using
                  (frontier_subset_closure : frontier (f.sourceCompact K) ⊆ _)
              exact (hfront.image hf.2.continuous).isClosed.isOpen_compl)⟩ :
              TopologicalSpace.Opens X)
          let T := f.localCompactCoverDomain K S hf.2.continuous
          T ≤ U → ∀ W : Set X, MeasurableSet W → W ⊆ T →
            InjOn f.totalize W → f.totalize '' W ⊆ L →
            p.domainArea U W ≤ p.domainArea U (f.totalize '' W) + C) := by
  obtain ⟨E, hH, hcover⟩ :=
    f.exists_finite_branch_values_local_compact_covering hf hK hKsource
  let H : Set X := f.map '' frontier (f.sourceCompact K)
  refine ⟨E, hH, ?_⟩
  intro hLH
  obtain ⟨C, hC, hadvance⟩ :=
    p.exists_uniform_area_advance_of_remote_covering E.card hH hL hLH
  refine ⟨C, hC, ?_⟩
  intro U
  dsimp only
  let S := AreaDeficit.Surfaces.finiteRemovalDomain U E ⊓
    (⟨Hᶜ, hH.isClosed.isOpen_compl⟩ : TopologicalSpace.Opens X)
  let T := f.localCompactCoverDomain K S hf.2.continuous
  intro hTU W hW hWT hinj hfWL
  have hSE : (S : Set X) ⊆ (E : Set X)ᶜ := by
    intro x hx
    exact hx.1.2
  have hSH : (S : Set X) ⊆ Hᶜ := by
    intro x hx
    exact hx.2
  obtain ⟨F, hF, hcov, hFeq⟩ := hcover S hSE hSH
  exact hadvance E le_rfl U T hTU F hF hcov f.totalize
    (f.measurable_totalize hf.2.continuous) hFeq W hW hWT hinj hfWL

/-- Finite-puncture form of the compact local-model estimate.  The covering
domain and its inclusion in the old punctured model are constructed
internally from forward invariance of the boundary-puncture stage. -/
theorem exists_uniform_area_advance_of_local_compact_finite_models
    (p : AreaDeficit.Surfaces.DiscCover X)
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (V : TopologicalSpace.Opens X) (hVsource : (V : Set X) ⊆ f.source)
    {K L : Set X} (hK : IsCompact K) (hKsource : K ⊆ f.source)
    (hKV : K ⊆ V) (hL : IsCompact L) :
    ∃ (E : Finset X),
      IsCompact (f.map '' frontier (f.sourceCompact K)) ∧
      (Disjoint L (f.map '' frontier (f.sourceCompact K)) →
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
        ∀ (P : Finset X),
          (∀ x (hx : x ∈ V), x ∈ P → f.map ⟨x, hVsource hx⟩ ∈ P) →
          ∀ W : Set X, MeasurableSet W → W ⊆ interior K →
            InjOn f.totalize W → f.totalize '' W ⊆ L →
            (∀ x ∈ W, f.totalize x ∉ P ∪ E ∧
              f.totalize x ∉ f.map '' frontier (f.sourceCompact K)) →
            p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain P) W ≤
              p.domainArea (AreaDeficit.Surfaces.finitePunctureDomain P)
                (f.totalize '' W) + C) := by
  obtain ⟨E, hH, hcore⟩ :=
    f.exists_uniform_area_advance_of_local_compact_model p hf hK hKsource hL
  let H : Set X := f.map '' frontier (f.sourceCompact K)
  refine ⟨E, hH, ?_⟩
  intro hLH
  obtain ⟨C, hC, hadvance⟩ := hcore hLH
  refine ⟨C, hC, ?_⟩
  intro P hforward W hW hWK hinj himage havoid
  let U := AreaDeficit.Surfaces.finitePunctureDomain P
  let S := AreaDeficit.Surfaces.finiteRemovalDomain U E ⊓
    (⟨Hᶜ, hH.isClosed.isOpen_compl⟩ : TopologicalSpace.Opens X)
  let T := f.localCompactCoverDomain K S hf.2.continuous
  have hTU : T ≤ U :=
    f.localCompactCoverDomain_le_finitePunctureDomain hf.2.continuous
      V hVsource hKV P E hforward H hH.isClosed
  have hWT : W ⊆ T := by
    intro x hx
    apply f.mem_localCompactCoverDomain_of_mem_interior S hf.2.continuous
      hKsource (hWK hx)
    have hxsource : x ∈ f.source := hKsource (interior_subset (hWK hx))
    have htotal := f.totalize_eq hxsource
    have ha := havoid x hx
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change f.map ⟨x, hxsource⟩ ∉ P
      simpa only [htotal] using fun hp => ha.1 (Finset.mem_union_left E hp)
    · change f.map ⟨x, hxsource⟩ ∉ E
      simpa only [htotal] using fun he => ha.1 (Finset.mem_union_right P he)
    · change f.map ⟨x, hxsource⟩ ∉ H
      simpa only [htotal] using ha.2
  exact hadvance U hTU W hW hWT hinj himage

end SurfaceDynamics.LocalMap
