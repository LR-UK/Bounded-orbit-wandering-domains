module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseOpenEmbeddingArea

@[expose] public section

/-! # Compact target budgets pulled back through an open ambient embedding -/

open Set Function MeasureTheory Topology
open AreaDeficit.Surfaces
open scoped Manifold ENNReal

namespace SurfaceDynamics

variable {M N : Type*} [TopologicalSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) 1 N]
  [MeasurableSpace N] [BorelSpace N] [SecondCountableTopology N] [T2Space N] [LocallyCompactSpace N]

theorem exists_uniform_cross_ambient_gain_budget
    (q : ComponentwiseDiscCover N) (j : M → N) (hj : IsOpenEmbedding j)
    (D : TopologicalSpace.Opens N) (E : Finset M)
    {L : Set N} (hL : IsCompact L) (hLD : L ⊆ D) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ U : TopologicalSpace.Opens M,
      let Y := finiteRemovalDomain U E ⊓
        (⟨j ⁻¹' (D : Set N), D.isOpen.preimage hj.continuous⟩ : TopologicalSpace.Opens M)
      (q.domainAreaGain
        ⟨j '' (U : Set M), hj.isOpenMap _ U.isOpen⟩
        ⟨j '' (Y : Set M), hj.isOpenMap _ Y.isOpen⟩).comap j (j ⁻¹' L) ≤ B := by
  classical
  let E' := E.image j
  obtain ⟨B, hB, hb⟩ := q.compact_finite_remote_removal_gain E' D.isOpen.isClosed_compl hL
    (disjoint_left.mpr (fun _ hx hn => hn (hLD hx)))
  refine ⟨B, hB, ?_⟩
  intro U
  let U' : TopologicalSpace.Opens N := ⟨j '' (U : Set M), hj.isOpenMap _ U.isOpen⟩
  let Y := finiteRemovalDomain U E ⊓
    (⟨j ⁻¹' (D : Set N), D.isOpen.preimage hj.continuous⟩ : TopologicalSpace.Opens M)
  have hY : (⟨j '' (Y : Set M), hj.isOpenMap _ Y.isOpen⟩ : TopologicalSpace.Opens N) =
      finiteRemovalDomain U' E' ⊓ D := by
    ext x
    constructor
    · rintro ⟨a, ⟨⟨haU, haE⟩, haD⟩, rfl⟩
      refine ⟨⟨⟨a, haU, rfl⟩, ?_⟩, haD⟩
      intro hh
      obtain ⟨b, hbE, hba⟩ := Finset.mem_image.mp hh
      exact haE (hj.injective hba ▸ hbE)
    · rintro ⟨⟨⟨a, haU, rfl⟩, haE⟩, haD⟩
      exact ⟨a, ⟨⟨haU, fun he => haE (Finset.mem_image.mpr ⟨a, he, rfl⟩)⟩, haD⟩, rfl⟩
  have hD : (⟨(D : Set N)ᶜᶜ, D.isOpen.isClosed_compl.isOpen_compl⟩ :
      TopologicalSpace.Opens N) = D := by ext x; simp
  have hbound : q.domainAreaGain U' (finiteRemovalDomain U' E' ⊓ D) L ≤ B := by
    simpa only [hD] using hb U'
  change (q.domainAreaGain U' _).comap j (j ⁻¹' L) ≤ B
  rw [hY, Measure.comap_apply j hj.injective
    (fun S hS => hj.measurableEmbedding.measurableSet_image.mpr hS) _
    (hL.measurableSet.preimage hj.continuous.measurable)]
  exact (measure_mono (image_preimage_subset j L)).trans hbound

end SurfaceDynamics
