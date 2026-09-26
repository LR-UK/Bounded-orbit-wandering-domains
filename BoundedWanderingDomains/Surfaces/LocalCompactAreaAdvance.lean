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
    ∃ (E : Finset X) (H : Set X) (hH : IsCompact H),
      Disjoint L H → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
        ∀ U : TopologicalSpace.Opens X,
          let S := AreaDeficit.Surfaces.finiteRemovalDomain U E ⊓
            (⟨Hᶜ, hH.isClosed.isOpen_compl⟩ :
              TopologicalSpace.Opens X)
          let T := f.localCompactCoverDomain K S hf.2.continuous
          T ≤ U → ∀ W : Set X, MeasurableSet W → W ⊆ T →
            InjOn f.totalize W → f.totalize '' W ⊆ L →
            p.domainArea U W ≤ p.domainArea U (f.totalize '' W) + C := by
  obtain ⟨E, H, hH, hcover⟩ :=
    f.exists_finite_branch_values_local_compact_covering hf hK hKsource
  refine ⟨E, H, hH, ?_⟩
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

end SurfaceDynamics.LocalMap

#print axioms SurfaceDynamics.LocalMap.exists_uniform_area_advance_of_local_compact_model
